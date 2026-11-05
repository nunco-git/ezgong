import os, sys, time, tempfile, queue, threading, base64, io
sys.path.insert(0, "smart-explorer")
import smart_explorer as S, tkinter as tk
d = tempfile.mkdtemp()
for i in range(30):
    sub = os.path.join(d, "예산폴더%d" % (i % 3))
    os.makedirs(sub, exist_ok=True)
    open(os.path.join(sub, "doc%d.txt" % i), "w", encoding="utf-8").write("내용 %d 예산집행" % i)
open(os.path.join(d, "예산보고.txt"), "w", encoding="utf-8").write("아무거나")
# name worker
q = queue.Queue(); st = threading.Event()
S.name_worker(d, [S.make_pattern("예산", True)], True, q, st)
hits = []
while not q.empty():
    m = q.get()
    if m[0] == "hit": hits.append(m[1])
    if m[0] == "done": print("done", m[1:])
print("name hits", len(hits), "dirs", sum(h["is_dir"] for h in hits), flush=True)
print("OK name" if len(hits) == 4 and sum(h["is_dir"] for h in hits) == 3 else "FAIL name", flush=True)
inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
print("ocr cfg", app.indexer.cfg.get("ocr"), app.s.get("index_ocr_v109"), flush=True)
ix = app.indexer
ix.stop_flag.set(); time.sleep(0.5); ix.stop_flag.clear()
ix.folders = lambda: [d]
ix._wait_idle = lambda: True
ix._pass(); print("pass1 total", ix.total, "read", ix.read, ix.summary(), flush=True)
ix._pass(); print("pass2 read", ix.read, flush=True)
p = app.panes[0]
p.navigate(d); p.query_var.set("예산")
def go():
    p.start("name")
    def chk():
        if p.busy(): return root.after(200, chk)
        root.after(500, shot)
    root.after(300, chk)
def shot():
    print("pane hits", len(p.hits), p.status_var.get(), flush=True)
    from PIL import ImageGrab
    root.update()
    x, y, w, h = root.winfo_rootx(), root.winfo_rooty(), root.winfo_width(), root.winfo_height()
    im = ImageGrab.grab((x, y, x + w, y + min(h, 500)))
    b = io.BytesIO(); im.save(b, "PNG")
    print("IMG64:" + base64.b64encode(b.getvalue()).decode(), flush=True)
    p.start("body")
    def chk2():
        if p.busy(): return root.after(200, chk2)
        print("body hits", len(p.hits), p.status_var.get(), "mode", p.search_mode, flush=True)
        os._exit(0)
    root.after(300, chk2)
root.after(1500, go)
root.after(60000, lambda: os._exit(1))
root.mainloop()
