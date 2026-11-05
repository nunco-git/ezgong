import json, urllib.request, urllib.parse, io, base64, sys
from PIL import Image, ImageDraw
UA = {"User-Agent": "SmartgongWallpaperPicker/1.0 (smartgongmaster@gmail.com)"}
def api(params):
    params.update(format="json")
    u = "https://commons.wikimedia.org/w/api.php?" + urllib.parse.urlencode(params)
    return json.load(urllib.request.urlopen(urllib.request.Request(u, headers=UA), timeout=30))
queries = ["mountain lake landscape", "sunrise over sea", "forest path sunlight", "cherry blossom tree",
           "snowy mountains landscape", "green meadow blue sky", "autumn forest colors", "tropical beach",
           "Korea landscape", "starry night sky landscape", "lavender field", "waterfall forest"]
cands = []
for q in queries:
    r = api({"action": "query", "generator": "search", "gsrsearch": q + " filetype:bitmap", "gsrnamespace": 6,
             "gsrlimit": 40, "prop": "imageinfo", "iiprop": "url|size|extmetadata", "iiurlwidth": 400})
    n = 0
    for pg in sorted(r.get("query", {}).get("pages", {}).values(), key=lambda p: p.get("index", 0)):
        ii = pg["imageinfo"][0]; md = ii.get("extmetadata", {})
        lic = md.get("LicenseShortName", {}).get("value", "")
        if not (lic.startswith("CC0") or lic.lower().startswith("public domain")):
            continue
        w, h = ii["width"], ii["height"]
        if w < 1600 or not (1.3 <= w / h <= 1.9):
            continue
        cands.append({"q": q, "title": pg["title"], "url": ii["url"], "thumb": ii["thumburl"], "lic": lic,
                      "artist": md.get("Artist", {}).get("value", "")[:80], "w": w, "h": h})
        n += 1
        if n >= 4:
            break
print("count", len(cands), flush=True)
json.dump(cands, open("cands.json", "w"), ensure_ascii=False)
# contact sheet
cols = 6; tw, th = 240, 150
rows = (len(cands) + cols - 1) // cols
sheet = Image.new("RGB", (cols * tw, rows * (th + 16)), "white")
d = ImageDraw.Draw(sheet)
for i, c in enumerate(cands):
    try:
        im = Image.open(io.BytesIO(urllib.request.urlopen(urllib.request.Request(c["thumb"], headers=UA), timeout=30).read())).convert("RGB")
        im = im.resize((tw - 4, th - 4))
        sheet.paste(im, ((i % cols) * tw + 2, (i // cols) * (th + 16) + 2))
    except Exception as e:
        pass
    d.text(((i % cols) * tw + 4, (i // cols) * (th + 16) + th), str(i), fill="black")
for i, c in enumerate(cands):
    print("C", i, c["lic"], c["w"], c["h"], c["title"], flush=True)
b = io.BytesIO(); sheet.save(b, "JPEG", quality=70)
enc = base64.b64encode(b.getvalue()).decode()
for i in range(0, len(enc), 4000):
    print("SHEET:" + enc[i:i + 4000], flush=True)
