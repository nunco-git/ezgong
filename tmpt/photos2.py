import json, urllib.request, io, base64, os, time
from PIL import Image
UA = {"User-Agent": "SmartgongWallpaperPicker/1.0 (smartgongmaster@gmail.com)"}
c = json.load(open("cands.json"))
pick = [(0, "호수"), (2, "숲길"), (6, "벚꽃"), (9, "설산"), (12, "단풍"), (16, "바다"), (20, "라벤더"), (22, "숲"), (18, "밤하늘")]
out = []
for i, name in pick:
    x = c[i]
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
    b = io.BytesIO(); im.save(b, "JPEG", quality=80, optimize=True, progressive=True)
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
