import json, urllib.request, io, base64, os, time
from PIL import Image
UA = {"User-Agent": "SmartgongWallpaperPicker/1.0 (smartgongmaster@gmail.com)"}
import urllib.parse
pick = [("File:Lake Mountain Landscape.jpg", "호수"), ("File:Forest Path Sunset.jpg", "숲길"),
        ("File:Cherry tree blossom 2007 G1.JPG", "벚꽃"), ("File:Marmolada, Italy.jpg", "설산"),
        ("File:Autumn Colors on the Salmon River Ranger District (51889980461).jpg", "단풍"),
        ("File:Ginowan Tropical Beach.JPG", "바다"), ("File:Lavender field in bloom.jpg", "라벤더"),
        ("File:Forests at Athirapally Waterfall.jpg", "숲"), ("File:Ryan Ranch at Night (53434367775).jpg", "밤하늘")]
out = []
for title, name in pick:
    u = "https://commons.wikimedia.org/w/api.php?" + urllib.parse.urlencode({"action": "query", "titles": title,
        "prop": "imageinfo", "iiprop": "url|extmetadata", "format": "json"})
    pg = list(json.load(urllib.request.urlopen(urllib.request.Request(u, headers=UA), timeout=30))["query"]["pages"].values())[0]
    ii = pg["imageinfo"][0]
    x = {"title": title, "url": ii["url"], "lic": ii["extmetadata"]["LicenseShortName"]["value"]}
    for t in range(4):
        try:
            data = urllib.request.urlopen(urllib.request.Request(x["url"], headers=UA), timeout=60).read(); break
        except Exception as e:
            print("retry", e, flush=True); time.sleep(5)
    im = Image.open(io.BytesIO(data)).convert("RGB")
    W, H = 1600, 1000
    s = max(W / im.width, H / im.height)
    im = im.resize((round(im.width * s), round(im.height * s)), Image.LANCZOS)
    l, t_ = (im.width - W) // 2, (im.height - H) // 2
    im = im.crop((l, t_, l + W, t_ + H))
    for q in (80, 72, 64, 56, 48):                       # 한 장에 300KB 이하가 되도록
        b = io.BytesIO(); im.save(b, "JPEG", quality=q, optimize=True, progressive=True)
        if len(b.getvalue()) <= 300 * 1024:
            break
    print(name, len(b.getvalue()), flush=True)
    src = "https://commons.wikimedia.org/wiki/" + urllib.parse.quote(x["title"].replace(" ", "_")) if False else x["title"]
    out.append((name, f'{x["title"][5:]} ({x["lic"]}, Wikimedia Commons)', base64.b64encode(b.getvalue()).decode()))
with open("photo_walls.py", "w", encoding="utf-8") as f:
    f.write('"""기본 배경 사진 — 모두 Wikimedia Commons의 퍼블릭 도메인(CC0·Public domain) 사진이라\n'
            '출처 표시 없이 자유롭게 써도 됩니다. 1600x1000으로 잘라 JPEG로 넣었습니다."""\n\nPHOTO_WALLS = [\n')
    for n, cr, d in out:
        f.write(f"    ({n!r}, {cr!r},\n     {d!r}),\n")
    f.write("]\n")
print("size", os.path.getsize("photo_walls.py"))
