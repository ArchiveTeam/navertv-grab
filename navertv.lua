local urlparse = require("socket.url")
local https = require("ssl.https")
local cjson = require("cjson")
local utf8 = require("utf8")
local html_entities = require("htmlEntities")
local basexx = require("basexx")
local openssl_digest = require("openssl.digest")
local openssl_hmac = require("openssl.hmac")
local socket = require("socket")

local item_dir = os.getenv("item_dir")
local warc_file_base = os.getenv("warc_file_base")
local item_type = nil
local item_name = nil
local item_value = nil

local url_count = 0
local tries = 0
local downloaded = {}
local addedtolist = {}
local abortgrab = false
local killgrab = false
local logged_response = false
local status_code = 0
local content_type = ""

local discovered_outlinks = {}
local discovered_items = {}
local bad_items = {}
local ids = {}

local retry_url = false
local context = {}
local warc_digests = {}

local high_quality = {}
for item in io.lines("high-quality.txt") do
  high_quality[string.lower(item)] = true
end

local item_patterns = {
  ["^https?://apis%.naver%.com/now_web2/now_web_api/v1/clips/([0-9]+)/play%-info%?"] = "video",
  ["^https?://apis%.naver%.com/now_web2/now_web_api/v1/channel/([^/%?]+)/info%?"] = "channel",
  ["^https?://apis%.naver%.com/now_web2/now_web_api/v1/playlist/([0-9]+)%?"] = "playlist",
  ["^https?://apis%.naver%.com/now_web2/now_web_api/v1/search%?q=([^&]+)"] = "search",
  ["^https?://tv%.naver%.com/search%?.-query=([^&]+)"] = "search",
  ["^https?://tv%.naver%.com/v/([0-9]+)/*$"] = "video",
  ["^https?://tv%.naver%.com/v/([0-9]+)%?"] = "video",
  ["^https?://tv%.naver%.com/embed/([0-9]+)/*$"] = "video",
  ["^https?://tv%.naver%.com/embed/([0-9]+)%?"] = "video",
  ["^https?://tv%.naver%.com/h/([0-9]+)/*$"] = "video",
  ["^https?://tv%.naver%.com/h/([0-9]+)%?"] = "video",
  ["^https?://tv%.naver%.com/[^/%?]+%?.-playlistNo=([0-9]+)"] = "playlist",
  ["^https?://tv%.naver%.com/([0-9a-zA-Z_%.%-]+)/*$"] = "channel",
  ["^https?://tv%.naver%.com/([0-9a-zA-Z_%.%-]+)%?tab=[a-z]+$"] = "channel",
  ["^https?://tv%.naver%.com/([0-9a-zA-Z_%.%-]+)%?tab=[a-z]+&order=[A-Z]+$"] = "channel",
  ["^https?://([0-9a-z%-]*phinf%.pstatic%.net/[^#]+)$"] = "media",
  ["^https?://(resources%-rmcnmv%.pstatic%.net/navertv/[^%?]+%.jpg)$"] = "media",
  ["^https?://(resources%-rmcnmv%.pstatic%.net/navertv/[^%?]+%.jpg%?[^#]*)$"] = "media",
  ["^https?://(resources%-rmcnmv%.akamaized%.net/navertv/[^%?]+%.jpg)$"] = "media",
  ["^https?://(resources%-rmcnmv%.akamaized%.net/navertv/[^%?]+%.jpg%?[^#]*)$"] = "media",
  ["^https?://(s%.pstatic%.net/dthumb%.phinf/%?[^#]+)$"] = "media",
  ["^https?://(livecloud%-thumb%.akamaized%.net/[^#]+)$"] = "media",
  ["^https?://(static%-now%.pstatic%.net/[^#]+)$"] = "media",
  ["^https?://(static%-clipcreators%.pstatic%.net/[^#]+)$"] = "media",
  ["^https?://(hangeul%.pstatic%.net/[^#]+)$"] = "media",
  ["^https?://(ssl%.pstatic%.net/spi/[^#]+)$"] = "media",
  ["^https?://(ssl%.pstatic%.net/static%.cbox/[^#]+)$"] = "media",
  ["^https?://(static%-feedback%.pstatic%.net/css/cbox/[^#]+)$"] = "media",
  ["^https?://(s%.pstatic%.net/static/[^#]+)$"] = "media",
  ["^https?://(link%.naver%.com/assets/[^#]+)$"] = "media",
  ["^https?://(m%.naver%.com//?shorts/assets/[^#]+)$"] = "media",
  ["^https?://(clip%.naver%.com/assets/[^#]+)$"] = "media",
  ["^https?://(clip%-viewer%.naver%.com/assets/[^#]+)$"] = "media",
}

abort_item = function(item)
  abortgrab = true
  if not item then
    item = item_name
  end
  if not bad_items[item] then
    io.stdout:write("Aborting item " .. item .. ".\n")
    io.stdout:flush()
    bad_items[item] = true
  end
end

kill_grab = function(item)
  io.stdout:write("Aborting crawling.\n")
  io.stdout:flush()
  killgrab = true
end

read_file = function(file)
  if file then
    local f = assert(io.open(file, "rb"))
    local body = f:read("*all")
    f:close()
    return body
  else
    return ""
  end
end

processed = function(url)
  if downloaded[url] or addedtolist[url] then
    return true
  end
  return false
end

discover_item = function(target, item)
  if item ~= item_name and not target[item] then
    target[item] = true
    return true
  end
  return false
end

percent_encode_url = function(newurl)
  return string.gsub(newurl, "(.)", function(c)
    local b = string.byte(c)
    if b < 32 or b > 126 then
      return string.format("%%%02X", b)
    end
    return c
  end)
end

find_item = function(url)
  for pattern, type_ in pairs(item_patterns) do
    local value = string.match(url, pattern)
    if value then
      if type_ == "search" then
        value = string.gsub(value, "%+", " ")
      end
      if type_ ~= "media" then
        value = urlparse.unescape(value)
      else
        value = string.gsub(value, "^resources%-rmcnmv%.akamaized%.net/", "resources-rmcnmv.pstatic.net/")
      end
      return {
        ["value"]=value,
        ["type"]=type_
      }
    end
  end
end

finish_item = function()
  if item_name then
    local video_archived = false
    for url, checked in pairs(context["digests"]) do
      if checked ~= true and not warc_digests[checked] then
        error("WARC digest does not match downloaded data.")
      end
      if string.match(string.lower(url) .. "?", "^https?://[^%?]+%.ts%?") then
        video_archived = true
      end
    end
    if item_type == "video"
      and not abortgrab
      and not context["missing"]
      and not video_archived then
      error("No video archived.")
    end
  end
end

set_item = function(url)
  if ids[string.lower(url)] then
    return nil
  end
  local found = find_item(url)
  if found then
    local new_item_type = found["type"]
    local new_item_value = found["value"]
    local new_item_name = percent_encode_url(new_item_type .. ":" .. new_item_value)
    if new_item_name ~= item_name then
      finish_item()
      ids = {}
      context = {
        ["api_urls"]={},
        ["digests"]={}
      }
      item_value = new_item_value
      item_type = new_item_type
      ids[string.lower(item_value)] = true
      ids[string.lower(url)] = true
      abortgrab = false
      tries = 0
      retry_url = false
      item_name = new_item_name
      print("Archiving item " .. item_name)
    end
  end
end

allowed = function(url)
  local lower = string.lower(url)

  if string.match(lower .. "?", "^https?://[^%?]+%.gif%?")
    or string.match(lower .. "?", "^https?://[^%?]+/trailer/[^%?]+%.mp4%?")
    or string.match(lower .. "?", "^https?://[^%?]+/favicon%.ico%?") then
    return false
  end

  if ids[lower] then
    return true
  end

  if string.match(lower .. "?", "^https?://[^%?]+%.mp4%?")
    or string.match(lower .. "?", "^https?://[^%?]+%.m3u8%?")
    or string.match(lower .. "?", "^https?://[^%?]+%.ts%?") then
    return false
  end

  for _, path in pairs({
    "chart",
    "embed",
    "f",
    "h",
    "i",
    "l",
    "my",
    "r",
    "rp",
    "search",
    "shareplayer",
    "v",
    "watch"
  }) do
    if (
      string.match(lower, "^https?://tv%.naver%.com/" .. path .. "/*$")
      or string.match(lower, "^https?://tv%.naver%.com/" .. path .. "%?")
    ) and not (path == "search" and string.match(url, "[%?&]query=[^&]+")) then
      return false
    end
  end

  local found = find_item(url)
  if found then
    local new_item = percent_encode_url(found["type"] .. ":" .. found["value"])
    if new_item ~= item_name then
      discover_item(discovered_items, new_item)
      return false
    end
    return true
  end

  if not (
    string.match(lower, "^https?://[^/]*%.naver%.com/")
    or string.match(lower, "^https?://[^/]*%.pstatic%.net/")
    or string.match(lower, "^https?://[^/]*%.akamaized%.net/")
  ) then
    discover_item(discovered_outlinks, string.match(percent_encode_url(url), "^([^%s]+)"))
    return false
  end

  if item_type == "search" then
    local query = string.match(url, "^https?://apis%.naver%.com/now_web2/now_web_api/v1/search/[a-z]+%?q=([^&]+)")
      or string.match(url, "^https?://tv%.naver%.com/_next/data/[^/]+/search%.json%?query=([^&]+)")
    if not query then
      return false
    end
    query = string.gsub(query, "%+", " ")
    return urlparse.unescape(query) == item_value
  end

  for _, pattern in pairs({
    "([0-9]+)",
    "([^/%?&;=]+)"
  }) do
    for identifier in string.gmatch(url, pattern) do
      identifier = urlparse.unescape(identifier)
      if ids[string.lower(identifier)] then
        return true
      end
    end
  end

  return false
end

wget.callbacks.download_child_p = function(urlpos, parent, depth, start_url_parsed, iri, verdict, reason)
  return false
end

decode_codepoint = function(newurl)
  newurl = string.gsub(
    newurl, "\\[uU]([0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])",
    function(s)
      return utf8.char(tonumber(s, 16))
    end
  )
  return newurl
end

wget.callbacks.get_urls = function(file, url, is_css, iri)
  local urls = {}
  local html = nil
  local json = nil

  downloaded[url] = true

  if abortgrab then
    return {}
  end

  local function fix_case(newurl)
    if not string.match(newurl, "^https?://[^/]") then
      return newurl
    end
    if string.match(newurl, "^https?://[^/]+$") then
      newurl = newurl .. "/"
    end
    local a, b = string.match(newurl, "^(https?://[^/]+/)(.*)$")
    return string.lower(a) .. b
  end

  local function check(newurl, headers)
    if not newurl then
      newurl = ""
    end
    newurl = html_entities.decode(decode_codepoint(newurl))
    newurl = string.gsub(newurl, "\\/", "/")
    newurl = string.match(newurl, "^%s*(.-)%s*$")
    newurl = fix_case(newurl)
    if not string.match(newurl, "^https?://") or string.match(newurl, "[%s\\]") then
      return nil
    end
    local url = string.match(newurl, "^([^#]+)")
    local url_ = url
    while string.match(url_, "&amp;") do
      url_ = string.gsub(url_, "&amp;", "&")
    end
    if not processed(url_) and allowed(url_) then
      table.insert(urls, {
        url=url_,
        headers=headers or {}
      })
      addedtolist[url_] = true
      addedtolist[url] = true
      return true
    end
  end


  local function checknewurl(newurl)
    if not newurl then
      newurl = ""
    end
    newurl = decode_codepoint(newurl)
    if string.match(newurl, "['\"><]") then
      return nil
    end
    if string.match(newurl, "^https?:////") then
      check((string.gsub(newurl, ":////", "://")))
    elseif string.match(newurl, "^https?://") then
      check(newurl)
    elseif string.match(newurl, "^https?:\\/\\?/") then
      check((string.gsub(newurl, "\\", "")))
    elseif string.match(newurl, "^\\/\\/") then
      checknewurl(string.gsub(newurl, "\\", ""))
    elseif string.match(newurl, "^//") then
      check(urlparse.absolute(url, newurl))
    elseif string.match(newurl, "^\\/") then
      checknewurl(string.gsub(newurl, "\\", ""))
    elseif string.match(newurl, "^/") then
      check(urlparse.absolute(url, newurl))
    elseif string.match(newurl, "^%.%./") then
      if string.match(url, "^https?://[^/]+/[^/]+/") then
        check(urlparse.absolute(url, newurl))
      else
        checknewurl(string.match(newurl, "^%.%.(/.+)$"))
      end
    elseif string.match(newurl, "^%./") then
      check(urlparse.absolute(url, newurl))
    end
  end

  local function checknewshorturl(newurl)
    newurl = decode_codepoint(newurl)
    if string.match(newurl, "['\"><]") then
      return nil
    end
    if string.match(newurl, "^%?") then
      check(urlparse.absolute(url, newurl))
    elseif not (
      string.match(newurl, "^https?:\\?/\\?//?/?")
      or string.match(newurl, "^[/\\]")
      or string.match(newurl, "^%./")
      or string.match(newurl, "^[jJ]ava[sS]cript:")
      or string.match(newurl, "^[mM]ail[tT]o:")
      or string.match(newurl, "^vine:")
      or string.match(newurl, "^android%-app:")
      or string.match(newurl, "^ios%-app:")
      or string.match(newurl, "^data:")
      or string.match(newurl, "^irc:")
      or string.match(newurl, "^%${")
    ) then
      check(urlparse.absolute(url, newurl))
    end
  end

  local function force_check(newurl)
    local found = find_item(newurl)
    if not found or found["type"] ~= "media" then
      ids[string.lower(newurl)] = true
    end
    check(newurl)
  end

  local function check_api(newurl)
    newurl = "https://apis.naver.com/now_web2/now_web_api/v1" .. newurl
    if not context["api_urls"][newurl] then
      local msgpad = string.format("%.0f", socket.gettime() * 1000)
      local md = openssl_hmac.new("nbxvs5nwNG9QKEWK0ADjYA4JZoujF4gHcIwvoCxFTPAeamq5eemvt5IWAYXxrbYM", "sha1")
        :final(string.sub(newurl, 1, 255) .. msgpad)
      local separator = "?"
      if string.match(newurl, "%?") then
        separator = "&"
      end
      context["api_urls"][newurl] = newurl .. separator .. "msgpad=" .. msgpad .. "&md=" .. urlparse.escape(basexx.to_base64(md))
    end
    check(context["api_urls"][newurl])
  end

  local function escape_share(value)
    return string.gsub(value, "([^0-9a-zA-Z_%.!~%*'%(%)%-])", function(c)
      return string.format("%%%02X", string.byte(c))
    end)
  end

  local function scan_json(value, key)
    if key == "trailerUrl" or key == "clipTrailerUrl" then
      return nil
    end
    if type(value) == "table" then
      if item_type == "video" and value["clip"] and value["play"]
        and tostring(value["clip"]["clipNo"]) == item_value then
        check("https://play.rmcnmv.naver.com/vod/play/v2.0/" .. value["clip"]["videoId"] .. "?key=" .. urlparse.escape(value["play"]["inKey"]))
        check(
          "https://apis.naver.com/neonplayer/vodplay/v3/playback/" .. value["clip"]["videoId"]
          .. "?key=" .. urlparse.escape(value["play"]["inKey"])
          .. "&sid=2010"
          .. "&devt=html5_pc"
          .. "&stid=NAVERTV"
          .. "&scid=" .. item_value
        )
      end
      if item_type == "video" and value["clipInfo"]
        and tostring(value["clipInfo"]["clipNo"]) == item_value then
        local newurl = "https://m.naver.com//shorts/"
          .. "?serviceType=NTV"
          .. "&mediaId=" .. value["clipInfo"]["videoId"]
          .. "&recType=" .. value["recType"]
        if value["recId"] then
          newurl = newurl .. "&recId=" .. value["recId"]
        end
        if value["enableReverse"] then
          newurl = newurl .. "&enableReverse=true"
        end
        newurl = newurl .. "&panelType=sdk_ntv&entryPoint=https%3A%2F%2Ftv.naver.com"
        if value["recId"] == "CH" .. item_value then
          newurl = newurl .. "&clickNsc=navertv.chHome&clickArea=latestVideo.video"
        end
        check(
          newurl
          .. "&adUnitId=ntv_shortformviewer_web"
          .. "&viewerInfo=ntv_shortformviewer_web"
          .. "&embed=true"
          .. "&theme=light"
          .. "&viewMode=mobile"
        )
      end
      if value["clipNo"] and value["clipNo"] ~= cjson.null then
        check("https://tv.naver.com/v/" .. tostring(value["clipNo"]))
        if item_type == "video" and tostring(value["clipNo"]) == item_value and value["thumbnailImageUrl"] then
          check(value["thumbnailImageUrl"] .. "?type=now720b")
        end
        if value["orientation"] == "PORTRAIT" and value["thumbnailImageUrl"] then
          check(value["thumbnailImageUrl"] .. "?type=f364_560")
        end
      end
      if value["playlistNo"] and value["playlistNo"] ~= cjson.null
        and "playlist:" .. tostring(value["playlistNo"]) ~= item_name then
        check_api("/playlist/" .. tostring(value["playlistNo"]))
      end
      if value["channelId"] and value["channelId"] ~= cjson.null
        and (not value["serviceCode"] or value["serviceCode"] == "NAVER_TV") then
        check("https://tv.naver.com/" .. (value["displayChannelId"] ~= cjson.null and value["displayChannelId"] or value["channelId"]))
      end
      for k, v in pairs(value) do
        scan_json(v, k)
      end
    elseif type(value) == "string" and string.match(value, "^https?://") then
      check(value)
      if key == "channelProfileImageUrl" then
        check(value .. "?type=round_192_192")
      elseif key == "channelEmblemImageUrl" then
        check(string.match(value, "^[^%?]+") .. "?type=round_64_64")
      elseif key == "channelBannerImageUrlPc" then
        check(value .. "?type=pc_channel_banner")
      elseif key == "mobileImageUrl" then
        check(value .. "?type=f3040_140_blur")
      end
    end
  end

  local function check_video(videos)
    local selected = nil
    local current_height = nil
    local target_height = 270
    if context["high_quality"] then
      target_height = 720
    end
    for _, video in ipairs(videos) do
      local height = nil
      for _, label in ipairs(video["nvod:Label"]) do
        if label["@kind"] == "resolution" then
          height = tonumber(label["#text"])
        end
      end
      if (not context["high_quality"] or height <= 720)
        and (
          not selected
          or (video["SegmentTemplate"] and not selected["SegmentTemplate"])
          or (
            (video["SegmentTemplate"] or not selected["SegmentTemplate"])
            and (
              math.abs(height - target_height) < math.abs(current_height - target_height)
              or (
                math.abs(height - target_height) == math.abs(current_height - target_height)
                and height < current_height
              )
            )
          )
        ) then
        selected = video
        current_height = height
      end
    end
    if not selected then
      error("No video found.")
    end
    if selected["SegmentTemplate"] then
      local template = selected["SegmentTemplate"][1]
      local number = tonumber(template["@startNumber"])
      for _, segment in ipairs(template["SegmentTimeline"][1]["S"]) do
        local repeat_count = tonumber(segment["@r"] or 0)
        if repeat_count < 0 then
          error("Bad video data.")
        end
        for i = 0, repeat_count do
          local newurl = string.gsub(template["@media"], "%$RepresentationID%$", selected["@id"])
          newurl = string.gsub(newurl, "%$Number(%%0[0-9]+d)%$", function(format)
            return string.format(format, number)
          end)
          newurl = string.gsub(newurl, "%$Number%$", tostring(number))
          force_check(urlparse.absolute(selected["BaseURL"][1], newurl))
          number = number + 1
        end
      end
      if number == tonumber(template["@startNumber"]) then
        error("No video found.")
      end
    else
      force_check(selected["BaseURL"][1])
    end
  end

  local function scan_mpd(value, videos)
    if type(value) == "table" then
      if value["Representation"] then
        for _, video in ipairs(value["Representation"]) do
          table.insert(videos, video)
        end
      end
      if value["nvod:Source"] then
        local source = value["nvod:Source"][1]
        if source["@patternType"] == "sequence_pattern" then
          for page = 0, tonumber(value["nvod:Page"][1]["@total"]) - 1 do
            check((string.gsub(source["#text"], "#", tostring(page))))
          end
        elseif string.match(source["#text"], "^https?://") then
          force_check(source["#text"])
        end
      end
      if value["nvod:Cover"] then
        check(value["nvod:Cover"][1]["#text"])
      end
      if value["nvod:ThumbnailSet"] then
        check(string.match(value["nvod:ThumbnailSet"][1]["nvod:Thumbnail"][1]["nvod:Source"][1]["#text"], "^([^%?]+)"))
      end
      for _, child in pairs(value) do
        scan_mpd(child, videos)
      end
    end
  end

  if status_code == 404
    and string.match(url, "^https?://apis%.naver%.com/now_web2/now_web_api/v1/clips/[0-9]+/play%-info%?") then
    check("https://tv.naver.com/v/" .. item_value)
  end

  if allowed(url) and status_code < 300 then
    local resource = string.match(url, "^https?://resources%-rmcnmv%.pstatic%.net/(navertv/[^#]+)")
      or string.match(url, "^https?://resources%-rmcnmv%.akamaized%.net/(navertv/[^#]+)")
    if resource and (
      string.match(resource .. "?", "^navertv/[^%?]+%.jpg%?")
      or string.match(resource .. "?", "^navertv/[^%?]+%.vtt%?")
    ) then
      force_check("https://resources-rmcnmv.pstatic.net/" .. resource)
      force_check("https://resources-rmcnmv.akamaized.net/" .. resource)
    end

    if string.match(url, "^https?://me2do%.naver%.com/common/requestJsonpV2%?") then
      json = cjson.decode(string.match(read_file(file), "^[^(]+%((.+)%)%s*;?%s*$"))["result"]
      force_check(json["httpsUrl"])
    elseif string.match(url, "/oembed%?") then
      if string.match(url, "[%?&]format=json") then
        json = cjson.decode(read_file(file))
        check(json["thumbnail_url"])
        check(json["playerUrl"])
        check(json["author_url"])
      end
    elseif string.match(url, "^https?://apis%.naver%.com/now_web2/now_web_api/") then
      json = cjson.decode(read_file(file))["result"]
      if string.match(url, "/clips/[0-9]+/play%-info%?") then
        if tostring(json["clip"]["clipNo"]) ~= item_value then
          error("Inconsistent video data.")
        end
        context["high_quality"] = high_quality[item_name]
          or high_quality["channel:" .. string.lower(json["channel"]["channelId"])]
          or high_quality["channel:" .. string.lower(json["channel"]["displayChannelId"])]
        ids[string.lower(json["clip"]["videoId"])] = true
        if type(json["clip"]["shareUrl"]) == "string" and string.match(json["clip"]["shareUrl"], "^https?://naver%.me/") then
          force_check(json["clip"]["shareUrl"])
        end
        force_check(
          "https://me2do.naver.com/common/requestJsonpV2"
          .. "?_callback=window.spi_0"
          .. "&svcCode=0022"
          .. "&url=" .. escape_share("https://tv.naver.com/v/" .. item_value)
          .. "&"
        )
        scan_json(json)
        for _, tag in ipairs(json["clip"]["tags"]) do
          check("https://tv.naver.com/search?query=" .. urlparse.escape(tag))
        end
        check("https://tv.naver.com/embed/" .. item_value)
        check("https://tv.naver.com/embed/" .. item_value .. "?autoPlay=true")
        if json["clip"]["highlight"] then
          check("https://tv.naver.com/h/" .. item_value)
          check("https://tv.naver.com/h/" .. item_value .. "?recType=NTV&recId=CH" .. item_value .. "&enableReverse=true")
        end
        check_api("/clips/" .. item_value .. "/meta-info")
        check_api("/clips/" .. item_value .. "/playlist")
        check_api("/clips/" .. item_value .. "/vote-status")
      elseif string.match(url, "/clips/[0-9]+/meta%-info%?") then
        scan_json(json)
        if json["comment"]["enabled"] then
          local comment = json["comment"]
          for _, sort in pairs({
            "undefined",
            "best"
          }) do
            check(
              "https://apis.naver.com/now_web2/cbox/web_naver_list_advanced_jsonp.json"
              .. "?pool=cbox"
              .. "&lang=ko"
              .. "&ticket=" .. urlparse.escape(comment["ticketId"])
              .. "&objectId=" .. urlparse.escape(comment["objectId"])
              .. "&templateId=" .. urlparse.escape(comment["templateId"])
              .. "&likeItId=" .. item_value
              .. "&sort=" .. sort
              .. "&page=1"
              .. "&pageSize=20"
              .. "&pageType=more"
              .. "&moreParam.direction=next"
              .. "&moreParam.prev="
              .. "&moreParam.next="
            )
          end
        end
      elseif string.match(url, "/clips/[0-9]+/playlist%?") then
        scan_json(json)
      elseif string.match(url, "/channel/[^/]+/info%?") then
        scan_json(json)
        check_api("/channel/" .. item_value .. "/info-stat")
        check_api("/channel/" .. item_value .. "/playlists?page=1&pageSize=5")
        check_api("/channel/" .. item_value .. "/shorts?page=1&pageSize=14&order=RECENT")
        for _, order in pairs({
          "RECENT",
          "POPULAR",
          "LIKE"
        }) do
          check_api("/channel/" .. item_value .. "/general-clips?page=1&pageSize=30&order=" .. order)
          check_api("/channel/" .. item_value .. "/shorts?page=1&pageSize=30&order=" .. order)
          check("https://tv.naver.com/" .. item_value .. "?tab=clip&order=" .. order)
          check("https://tv.naver.com/" .. item_value .. "?tab=highlight&order=" .. order)
          if order ~= "LIKE" then
            check_api("/channel/" .. item_value .. "/general-clips?page=1&pageSize=10&order=" .. order)
          end
        end
        for _, tab in pairs({
          "home",
          "clip",
          "highlight",
          "playlist",
          "information"
        }) do
          check("https://tv.naver.com/" .. item_value .. "?tab=" .. tab)
        end
      elseif string.match(url, "/channel/[^/]+/[a-z%-]+%?page=") then
        scan_json(json)
        if #json["data"] > 0
          and not string.match(url, "[%?&]pageSize=10&")
          and not string.match(url, "[%?&]pageSize=14&") then
          local path = string.match(url, "/v1(.-)&msgpad=")
          check_api(string.gsub(path, "([%?&]page=)[0-9]+", "%1" .. tostring(json["pageRequest"]["page"] + 1)))
        end
      elseif string.match(url, "/v1/search%?") then
        scan_json(json)
        local query = urlparse.escape(item_value)
        local sort = string.match(url, "[%?&]sortKey=([^&]+)")
        for _, path in pairs({
          "/search/clips?q=" .. query .. "&clipContentType=LONGFORM",
          "/search/clips?q=" .. query .. "&clipContentType=SHORTFORM",
          "/search/lives?q=" .. query,
          "/search/channels?q=" .. query
        }) do
          check_api(path .. "&sortKey=" .. sort .. "&page=1&pageSize=50")
        end
        if sort == "rel" then
          check("https://tv.naver.com/search?query=" .. query)
          for _, order in pairs({"date", "playcount"}) do
            check_api("/search?q=" .. query .. "&sortKey=" .. order .. "&page=1&pageSize=50")
          end
        end
      elseif string.match(url, "/v1/search/") then
        scan_json(json)
        local page = tonumber(string.match(url, "[%?&]page=([0-9]+)"))
        if #json["data"] > 0 and page < 20 then
          local path = string.match(url, "/v1(.-)&msgpad=")
          check_api(string.gsub(path, "([%?&]page=)[0-9]+", "%1" .. tostring(page + 1)))
        end
      elseif string.match(url, "/playlist/") then
        scan_json(json)
        check("https://tv.naver.com/" .. json["channelId"] .. "?tab=playlist&playlistNo=" .. item_value)
        for _, clip in ipairs(json["clips"]) do
          force_check("https://tv.naver.com/v/" .. tostring(clip["clipNo"]) .. "?playlistNo=" .. item_value)
        end
      end
    elseif string.match(url, "^https?://creatorhub%-api%.naver%.com/api/v7%.0/clipviewer/card%?") then
      json = cjson.decode(read_file(file))["body"]["card"]["content"]
      local videos = {}
      scan_mpd(json["vod"]["playback"], videos)
      check_video(videos)
      check(json["endUrl"])
      check(json["mobileEndUrl"])
      check(json["contentWebModalUrl"])
      check(json["channel"]["homePcUrl"])
      local comment = json["interaction"]["comment"]
      if comment["exposeComment"] then
        force_check(comment["webModalUrl"])
        check(
          "https://apis.naver.com/commentBox/cbox/web_naver_list_json.json"
          .. "?ticket=" .. urlparse.escape(comment["ticket"])
          .. "&templateId=" .. urlparse.escape(comment["params"]["templateId"])
          .. "&pool=" .. urlparse.escape(comment["params"]["pool"])
          .. "&_cv="
          .. "&lang=ko"
          .. "&pageType=more"
          .. "&country="
          .. "&objectId=" .. urlparse.escape(comment["id"])
          .. "&categoryId="
          .. "&pageSize=20"
          .. "&indexSize=10"
          .. "&groupId="
          .. "&listType=OBJECT"
          .. "&page=1"
          .. "&initialize=true"
          .. "&followSize=5"
          .. "&userType="
          .. "&useAltSort=true"
          .. "&replyPageSize=10"
          .. "&sort=FAVORITE"
        )
        check(
          "https://apis.naver.com/clip-viewer-web/cbox/web_naver_rolling_cached_json"
          .. "?objectId=" .. urlparse.escape(comment["id"])
          .. "&ticket=" .. urlparse.escape(comment["ticket"])
          .. "&pool=" .. urlparse.escape(comment["params"]["pool"])
          .. "&templateId=" .. urlparse.escape(comment["params"]["templateId"])
          .. "&lang=ko"
          .. "&rollingType=MANAGER_LIKE"
        )
      end
    elseif string.match(url, "^https?://apis%.naver%.com/clip%-viewer%-web/cbox/") then
      scan_json(cjson.decode(read_file(file))["result"]["comments"])
    elseif string.match(url, "^https?://apis%.naver%.com/now_web2/cbox/")
      or string.match(url, "^https?://apis%.naver%.com/commentBox/cbox/") then
      local data = read_file(file)
      if string.match(url, "/now_web2/") then
        data = string.match(data, "^_callback%((.+)%)%s*;%s*$")
      end
      json = cjson.decode(data)["result"]
      scan_json(json["commentList"])
      for _, comment in ipairs(json["commentList"]) do
        if comment["replyCount"] > 0 then
          local newurl = string.gsub(url, "&sort=[^&]+", "")
          newurl = string.gsub(newurl, "&page=[0-9]+.*$",
            "&page=1"
            .. "&pageSize=10"
            .. "&parentCommentNo=" .. tostring(comment["commentNo"])
            .. "&pageType=more"
            .. "&moreParam.direction=next"
            .. "&moreParam.prev="
            .. "&moreParam.next="
          )
          check(newurl)
        end
      end
      local page = json["pageModel"]
      if page["page"] < page["totalPages"] then
        local newurl = string.gsub(url, "([%?&]page=)[0-9]+", "%1" .. tostring(page["page"] + 1))
        if string.match(url, "web_naver_list_advanced_jsonp") then
          newurl = string.gsub(newurl, "(&moreParam%.prev=)[^&]*", "%1" .. urlparse.escape(json["morePage"]["prev"]))
          newurl = string.gsub(newurl, "(&moreParam%.next=)[^&]*", "%1" .. urlparse.escape(json["morePage"]["next"]))
        end
        check(newurl)
      end
    elseif string.match(url, "^https?://creatorhub%-api%.naver%.com/api/v7%.0/clip/profiles") then
      json = cjson.decode(read_file(file))["body"]
      ids[string.lower(json["profileId"])] = true
      scan_json(json)
      check("https://creatorhub-api.naver.com/api/v7.0/clip/profiles/" .. json["profileId"])
    elseif string.match(url, "^https?://play%.rmcnmv%.naver%.com/vod/play/") then
      json = cjson.decode(read_file(file))
      if json["captions"] then
        for _, caption in ipairs(json["captions"]["list"]) do
          force_check(caption["source"])
        end
      end
      scan_json(json["thumbnails"]["list"])
      check(json["meta"]["cover"]["source"])
      for _, sprite in ipairs(json["thumbnails"]["sprites"]) do
        for page = 0, sprite["totalPage"] - 1 do
          check((string.gsub(sprite["source"], "#", tostring(page))))
        end
      end
    elseif string.match(url, "^https?://apis%.naver%.com/neonplayer/vodplay/v3/playback/") then
      local xml = read_file(file)
      local videos = {}
      for attributes, representation in string.gmatch(xml, "<Representation([^>]*)>(.-)</Representation>") do
        local video = {
          ["@id"]=string.match(attributes, '%sid="([^"]+)"'),
          ["nvod:Label"]={{
            ["@kind"]="resolution",
            ["#text"]=string.match(representation, '<nvod:Label kind="resolution">([0-9]+)</nvod:Label>')
          }},
          ["BaseURL"]={html_entities.decode(string.match(representation, "<BaseURL>(.-)</BaseURL>"))}
        }
        local template = string.match(representation, "<SegmentTemplate([^>]*)>")
        if template then
          local segments = {}
          for segment in string.gmatch(representation, "<S(%s+[^>]*)/>") do
            table.insert(segments, {
              ["@r"]=string.match(segment, '%sr="(%-?[0-9]+)"')
            })
          end
          video["SegmentTemplate"] = {{
            ["@media"]=html_entities.decode(string.match(template, '%smedia="([^"]+)"')),
            ["@startNumber"]=string.match(template, '%sstartNumber="([0-9]+)"'),
            ["SegmentTimeline"]={{
              ["S"]=segments
            }}
          }}
        end
        table.insert(videos, video)
      end
      check_video(videos)
      for newurl in string.gmatch(xml, '<nvod:Source type="[^"]+">(https?://[^<]+)</nvod:Source>') do
        force_check(html_entities.decode(newurl))
      end
      for newurl in string.gmatch(xml, '<nvod:Cover type="url">([^<]+)</nvod:Cover>') do
        check(html_entities.decode(newurl))
      end
      for sprite in string.gmatch(xml, "<nvod:SeekingThumbnail[^>]*>(.-)</nvod:SeekingThumbnail>") do
        local source = html_entities.decode(string.match(sprite, "<nvod:Source[^>]*>([^<]+)</nvod:Source>"))
        for page = 0, tonumber(string.match(sprite, '<nvod:Page total="([0-9]+)"')) - 1 do
          check((string.gsub(source, "#", tostring(page))))
        end
      end
    elseif string.match(url, "^https?://tv%.naver%.com/_next/data/") then
      scan_json(cjson.decode(read_file(file)))
    elseif string.match(content_type, "^text/html") then
      html = read_file(file)
      if string.match(url, "^https?://link%.naver%.com/bridge%?") then
        check(urlparse.unescape(string.match(url, "[%?&]url=([^&]+)")))
      elseif string.match(url, "^https?://m%.naver%.com//?shorts/%?") then
        local query = {}
        for key, value in string.gmatch(url, "[%?&]([^=&]+)=([^&]*)") do
          query[key] = value
        end
        local video_id = string.match(url, "[%?&]seedMediaId=([^&]+)")
          or string.match(url, "[%?&]mediaId=([^&]+)")
        local media_type = string.match(url, "[%?&]mediaType=([^&]+)") or "SHORT_FORM"
        if media_type == "VOD" then
          media_type = "SHORT_FORM"
        end
        local share_url = "https://m.naver.com/shorts/"
          .. "?seedMediaId=" .. video_id
          .. "&serviceType=NTV"
          .. "&recType=AIRS"
          .. "&panelType=share"
          .. "&clickNsc=share"
          .. "&adAllowed=Y"
        local params = '{"seedMediaId":"' .. video_id .. '"'
          .. ',"serviceType":"NTV"'
          .. ',"mediaType":"VOD"'
          .. ',"recType":"AIRS"'
          .. ',"recId":""'
          .. ',"panelType":"share"'
          .. ',"clickNsc":"share"'
          .. ',"adAllowed":"Y"}'
        share_url = "https://link.naver.com/bridge"
          .. "?url=" .. escape_share(share_url)
          .. "&dst=" .. escape_share(
            "naversearchapp://playshortform"
            .. "?params=" .. escape_share(params)
            .. "&version=55"
            .. "&sourceReferer=share"
          )
        force_check("https://me2do.naver.com/common/requestJsonpV2?_callback=window.spi_0&svcCode=0022&url=" .. escape_share(share_url) .. "&")
        check(
          "https://creatorhub-api.naver.com/api/v7.0/clipviewer/card"
          .. "?userInteraction=true"
          .. "&seedType=PERSONAL"
          .. "&serviceType=NAVER_TV"
          .. "&seedMediaId=" .. video_id
          .. "&mediaType=" .. media_type
          .. (query["panelType"] and "&panelType=" .. query["panelType"] or "")
          .. "&referer=" .. (query["entryPoint"] or "")
          .. "&recType=" .. (query["recType"] or "AIRS")
          .. (query["recId"] and "&recId=" .. query["recId"] or "")
          .. "&enableReverse=" .. (query["enableReverse"] or "false")
          .. "&adAllowed=false"
          .. (query["clickNsc"] and "&clickNsc=" .. query["clickNsc"] or "")
          .. (query["clickArea"] and "&clickArea=" .. query["clickArea"] or "")
          .. ((query["recType"] or "AIRS") == "AIRS" and "&recentWatchedHistory=" or "")
          .. "&deviceType=html5_mo"
          .. (query["embed"] == "true" and "&profileOverride=false" or "")
        )
        check("https://clip-viewer.naver.com/oembed/?seedMediaId=" .. video_id .. "&mediaType=" .. media_type .. "&serviceType=NTV")
      elseif string.match(url, "^https?://clip%-viewer%.naver%.com/oembed/%?")
        or string.match(url, "^https?://m%.naver%.com/shorts/oembed/%?") then
        local video_id = string.match(url, "[%?&]seedMediaId=([^&]+)")
          or string.match(url, "[%?&]mediaId=([^&]+)")
        local media_type = string.match(url, "[%?&]mediaType=([^&]+)") or "SHORT_FORM"
        if media_type == "VOD" then
          media_type = "SHORT_FORM"
        end
        check(
          "https://creatorhub-api.naver.com/api/v7.0/clipviewer/card"
          .. "?userInteraction=true"
          .. "&seedType=SPECIFIC"
          .. "&serviceType=NAVER_TV"
          .. "&mediaType=" .. media_type
          .. "&seedMediaId=" .. video_id
          .. "&recType=AIRS"
          .. "&adAllowed=false"
          .. "&clickNsc=oembed"
          .. "&referer=" .. urlparse.escape(url)
        )
      elseif item_type == "channel" and string.match(url, "^https?://clip%.naver%.com/@") then
        local profile = string.match(url, "^https?://clip%.naver%.com/@([^/%?]+)")
        ids[string.lower(profile)] = true
        check("https://creatorhub-api.naver.com/api/v7.0/clip/profiles?clipId=" .. urlparse.escape(profile))
      end
      for image_url in string.gmatch(html, '<meta[^>]+property="og:image"[^>]+content="([^"]+)"') do
        check(html_entities.decode(image_url))
      end
      for data in string.gmatch(html, '<script[^>]+id="__NEXT_DATA__"[^>]*>(.-)</script>') do
        json = cjson.decode(data)
        scan_json(json)
        if json["gssp"] then
          local parameter = string.match(json["page"], "%[([^%]]+)%]")
          if json["page"] == "/search" then
            check("https://tv.naver.com/_next/data/" .. json["buildId"] .. "/search.json?query=" .. urlparse.escape(item_value))
          elseif parameter then
            local parsed = urlparse.parse(url)
            local newurl = "https://tv.naver.com/_next/data/" .. json["buildId"] .. parsed["path"] .. ".json?"
            if parsed["query"] then
              newurl = newurl .. parsed["query"] .. "&"
            end
            check(newurl .. parameter .. "=" .. urlparse.escape(json["query"][parameter]))
          end
        end
      end
    elseif item_type == "media" and string.match(content_type, "^text/css") then
      html = read_file(file)
    end

    if html then
      for quote, quoted in pairs({
        ['"']=string.gsub(html, "&[qQ][uU][oO][tT];", '"'),
        ["'"]=string.gsub(html, "&#039;", "'")
      }) do
        for newurl in string.gmatch(quoted, "([^" .. quote .. "]+)") do
          checknewurl(newurl)
        end
        for _, attribute in pairs({"href", "src"}) do
          for newurl in string.gmatch(html, "[^%-]" .. attribute .. "=" .. quote .. "([^" .. quote .. "]+)" .. quote) do
            checknewshorturl(newurl)
          end
        end
      end
      for newurl in string.gmatch(html, "url%(([^%)]+)%)") do
        newurl = html_entities.decode(newurl)
        newurl = string.match(newurl, "^%s*(.-)%s*$")
        check(urlparse.absolute(url, string.gsub(newurl, "^['\"](.-)['\"]$", "%1")))
      end
      for _, pattern in pairs({
        "<loc%s*>(.-)</loc%s*>",
        "<[0-9a-zA-Z_%-]+:loc%s*>(.-)</[0-9a-zA-Z_%-]+:loc%s*>"
      }) do
        for newurl in string.gmatch(html, pattern) do
          check(string.match(newurl, "^%s*<!%[CDATA%[(.-)%]%]>%s*$") or newurl)
        end
      end
      for newurl in string.gmatch(html, '<link>(https?://[^<]+)</link>') do
        check(newurl)
      end
      for srcset in string.gmatch(html, 'srcset=["\']([^"\']+)') do
        for newurl in string.gmatch(srcset, "([^,%s]+)%s+[0-9.]+[wx]") do
          check(urlparse.absolute(url, newurl))
        end
      end
    end
  end

  return urls
end

wget.callbacks.dedup_response = function(url, digest)
  if context["digests"][url] then
    if digest ~= context["digests"][url] then
      error("WARC digest does not match downloaded data.")
    end
    context["digests"][url] = true
    warc_digests[digest] = true
  end
end

wget.callbacks.write_to_warc = function(url, http_stat)
  local headers = http_stat["response_headers"]["headers"]
  status_code = http_stat["statcode"]
  content_type = headers["content-type"] and string.lower(headers["content-type"][1]) or ""
  set_item(url["url"])

  url_count = url_count + 1
  io.stdout:write(url_count .. "=" .. status_code .. " " .. url["url"] .. " \n")
  io.stdout:flush()

  logged_response = true
  if not item_name then
    error("No item name found.")
  end

  if http_stat["res"] < 0 then
    return false
  end

  if not (
    status_code == 200
    or status_code == 302
    or status_code == 307
    or (
      status_code == 404
      and string.match(url["url"], "^https?://apis%.naver%.com/now_web2/now_web_api/v1/clips/[0-9]+/play%-info%?")
      and cjson.decode(read_file(http_stat["local_file"]))["statusCode"] == "CLIP_NOT_FOUND"
    )
  ) then
    retry_url = true
    return false
  end

  if status_code == 200 then
    if http_stat["len"] == 0
      or (http_stat["contlen"] >= 0 and http_stat["len"] ~= http_stat["contlen"]) then
      retry_url = true
      return false
    end
    if string.match(url["url"], "^https?://me2do%.naver%.com/common/requestJsonpV2%?") then
      local json = cjson.decode(string.match(read_file(http_stat["local_file"]), "^[^(]+%((.+)%)%s*;?%s*$"))
      if json["code"] ~= "200"
        or json["result"]["orgUrl"] ~= urlparse.unescape(string.match(url["url"], "[%?&]url=([^&]+)"))
        or not string.match(json["result"]["httpsUrl"], "^https://naver%.me/[^/%?]+$") then
        retry_url = true
        return false
      end
    elseif string.match(url["url"], "/oembed%?") then
      local html = read_file(http_stat["local_file"])
      if string.match(url["url"], "[%?&]format=json") then
        if cjson.decode(html)["type"] ~= "video" then
          retry_url = true
          return false
        end
      elseif not string.match(html, "<oembed>") then
        retry_url = true
        return false
      end
    elseif string.match(url["url"], "^https?://apis%.naver%.com/now_web2/now_web_api/") then
      local json = cjson.decode(read_file(http_stat["local_file"]))
      if json["statusCode"] ~= "SUCCESS" then
        retry_url = true
        return false
      end
      if string.match(url["url"], "/clips/[0-9]+/play%-info%?") then
        for _, channel in pairs({
          "tvnjoy",
          "tvndrama0",
          "yonhapnews",
          "channelanews",
          "yonhapnewstv",
          "tvchosunnews",
          "ytnnews24",
          "kbsnews",
          "sbsnews8",
          "imnews",
          "jtbcnews"
        }) do
          if json["result"]["channel"]["channelId"] == channel then
            print("Ignored channel " .. channel .. ".")
            abort_item()
            return false
          end
        end
      end
    elseif string.match(url["url"], "^https?://creatorhub%-api%.naver%.com/api/v7%.0/clipviewer/card%?") then
      local json = cjson.decode(read_file(http_stat["local_file"]))
      if json["header"]["code"] ~= 0
        or json["body"]["card"]["content"]["serviceType"] ~= "NTV"
        or tostring(json["body"]["card"]["content"]["contentId"]) ~= item_value then
        retry_url = true
        return false
      end
    elseif string.match(url["url"], "^https?://creatorhub%-api%.naver%.com/api/v7%.0/clip/profiles") then
      if cjson.decode(read_file(http_stat["local_file"]))["header"]["code"] ~= 0 then
        retry_url = true
        return false
      end
    elseif string.match(url["url"], "^https?://apis%.naver%.com/now_web2/cbox/")
      or string.match(url["url"], "^https?://apis%.naver%.com/commentBox/cbox/")
      or string.match(url["url"], "^https?://apis%.naver%.com/clip%-viewer%-web/cbox/") then
      local data = read_file(http_stat["local_file"])
      if string.match(url["url"], "/now_web2/") then
        data = string.match(data, "^_callback%((.+)%)%s*;%s*$")
      end
      local json = cjson.decode(data)
      if json["success"] ~= true then
        retry_url = true
        return false
      end
    elseif string.match(url["url"], "^https?://play%.rmcnmv%.naver%.com/vod/play/") then
      local json = cjson.decode(read_file(http_stat["local_file"]))
      if not json["videos"] or #json["videos"]["list"] == 0 then
        retry_url = true
        return false
      end
    elseif string.match(url["url"], "^https?://apis%.naver%.com/neonplayer/vodplay/v3/playback/") then
      local xml = read_file(http_stat["local_file"])
      if not string.match(xml, '<MPD[^>]+type="static"')
        or not string.match(xml, "</MPD>%s*$")
        or not string.match(xml, "<Representation ")
        or not ids[string.lower(string.match(xml, 'nvod:videoId="([^"]+)"') or "")] then
        retry_url = true
        return false
      end
    elseif string.match(url["url"], "%.m3u8%?") or string.match(url["url"], "%.m3u8$") then
      local html = read_file(http_stat["local_file"])
      if not string.match(html, "^#EXTM3U")
        or not (string.match(html, "#EXT%-X%-STREAM%-INF:") or string.match(html, "#EXT%-X%-ENDLIST")) then
        retry_url = true
        return false
      end
    end
    local sha1 = openssl_digest.new("sha1")
    local file = assert(io.open(http_stat["local_file"], "rb"))
    while true do
      local data = file:read(16 * 1024 * 1024)
      if not data then
        break
      end
      sha1:update(data)
    end
    file:close()
    sha1 = sha1:final()
    if headers["etag"] then
      local expected = string.match(headers["etag"][1], "^[0-9a-f]+_([0-9a-f]+)$")
      if expected and string.len(expected) == 40 and basexx.to_hex(sha1) ~= string.upper(expected) then
        error("File does not match etag.")
      end
    end
    context["digests"][url["url"]] = "sha1:" .. basexx.to_base32(sha1)
  elseif status_code == 404 then
    context["missing"] = true
  end

  if status_code >= 300 and status_code <= 399 then
    if not http_stat["newloc"] then
      retry_url = true
      return false
    end
  end

  if abortgrab then
    print("Not writing to WARC.")
    return false
  end
  retry_url = false
  tries = 0
  return true
end

wget.callbacks.httploop_result = function(url, err, http_stat)
  status_code = http_stat["statcode"]
  set_item(url["url"])

  if not logged_response then
    url_count = url_count + 1
    io.stdout:write(url_count .. "=" .. status_code .. " " .. url["url"] .. " \n")
    io.stdout:flush()
    retry_url = true
  end
  logged_response = false

  if killgrab then
    return wget.actions.ABORT
  end

  if not item_name then
    error("No item name found.")
  end

  if abortgrab then
    abort_item()
    return wget.actions.EXIT
  end

  local newloc = nil
  if status_code >= 300 and status_code <= 399 then
    if http_stat["newloc"] then
      newloc = urlparse.absolute(url["url"], http_stat["newloc"])
    end
  end

  if status_code == 0 or http_stat["res"] < 0 or retry_url then
    io.stdout:write("Server returned bad response. ")
    io.stdout:flush()
    tries = tries + 1
    local maxtries = 5
    if tries > maxtries then
      io.stdout:write(" Skipping.\n")
      io.stdout:flush()
      tries = 0
      abort_item()
      return wget.actions.EXIT
    end
    local sleep_time = math.random(
      math.floor(math.pow(2, tries-0.5)),
      math.floor(math.pow(2, tries))
    )
    io.stdout:write("Sleeping " .. sleep_time .. " seconds.\n")
    io.stdout:flush()
    os.execute("sleep " .. sleep_time)
    return wget.actions.CONTINUE
  else
    downloaded[url["url"]] = true
  end

  if newloc then
    if string.match(newloc, "^https?://[^/]+$") then
      newloc = newloc .. "/"
    end
    if not find_item(newloc) and (
      string.match(newloc, "^https?://clip%.naver%.com/")
      or string.match(newloc, "^https?://m%.naver%.com/shorts/")
      or (
        string.match(url["url"], "^https?://naver%.me/")
        and string.match(newloc, "^https?://link%.naver%.com/bridge%?")
      )
      or string.match(newloc, "^https?://[^/]*%.pstatic%.net/")
      or string.match(newloc, "^https?://[^/]*%.akamaized%.net/")
    ) then
      ids[string.lower(newloc)] = true
    end
    if processed(newloc) or not allowed(newloc) then
      tries = 0
      return wget.actions.EXIT
    end
    ids[string.lower(newloc)] = true
  end

  tries = 0

  return wget.actions.NOTHING
end

wget.callbacks.finish = function(start_time, end_time, wall_time, numurls, total_downloaded_bytes, total_download_time)
  finish_item()
  local function submit_backfeed(items, key)
    local tries = 0
    local maxtries = 5
    while tries < maxtries do
      if killgrab then
        return false
      end
      local body, code, headers, status = https.request(
        "https://legacy-api.arpa.li/backfeed/legacy/" .. key,
        items .. "\0"
      )
      if code == 200 and body ~= nil and cjson.decode(body)["status_code"] == 200 then
        io.stdout:write(string.match(body, "^(.-)%s*$") .. "\n")
        io.stdout:flush()
        return nil
      end
      io.stdout:write("Failed to submit discovered URLs." .. tostring(code) .. tostring(body) .. "\n")
      io.stdout:flush()
      os.execute("sleep " .. math.floor(math.pow(2, tries)))
      tries = tries + 1
    end
    kill_grab()
    error()
  end

  local file = io.open(item_dir .. "/" .. warc_file_base .. "_bad-items.txt", "w")
  for url, _ in pairs(bad_items) do
    file:write(url .. "\n")
  end
  file:close()
  for key, data in pairs({
    ["navertv-8ee74a0916b349ab"] = discovered_items,
    ["urls-b5d13f09a4f261ee"] = discovered_outlinks
  }) do
    print("queuing for", string.match(key, "^(.+)%-"))
    local items = nil
    local count = 0
    for item, _ in pairs(data) do
      print("found item", item)
      if items == nil then
        items = item
      else
        items = items .. "\0" .. item
      end
      count = count + 1
      if count == 1000 then
        submit_backfeed(items, key)
        items = nil
        count = 0
      end
    end
    if items ~= nil then
      submit_backfeed(items, key)
    end
  end
end

wget.callbacks.before_exit = function(exit_status, exit_status_string)
  if killgrab then
    return wget.exits.IO_FAIL
  end
  if abortgrab then
    abort_item()
  end
  return exit_status
end
