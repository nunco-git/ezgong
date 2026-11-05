import os, sys, time, tempfile, base64, io
sys.path.insert(0, "smart-explorer")
import smart_explorer as S, tkinter as tk
from PIL import ImageGrab
print("ocr engine", S.ocr_engine() is not None, "no_korean", S._ocr["no_korean"], S._ocr["error"], flush=True)
d = tempfile.mkdtemp()
fp = os.path.join(d, "보고서.txt"); open(fp, "w", encoding="utf-8").write("x")
inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
def grab(win, tag):
    win.update(); time.sleep(0.3); win.update()
    x, y, w, h = win.winfo_rootx(), win.winfo_rooty(), win.winfo_width(), win.winfo_height()
    im = ImageGrab.grab((x - 8, y - 32, x + w + 8, y + h + 8))
    b = io.BytesIO(); im.save(b, "PNG")
    print(tag + ":" + base64.b64encode(b.getvalue()).decode(), flush=True)
def step1():
    app.ocr_missing(force=True)
    grab(app._ocr_dlg.win, "IMG1")
    app._ocr_dlg.close()
    p = app.panes[0]
    dlg = S.RenameDialog(p, {"path": fp, "name": "보고서.txt"})
    dlg.entry.focus_force(); root.update()
    print("ime", S.ime_match_font(dlg.entry), flush=True)
    grab(dlg.win, "IMG2")
    dlg.win.destroy()
    ix = app.indexer
    ix.folders = lambda: [d]; ix._wait_idle = lambda: True
    ix.cfg["ocr"] = True
    app.s.pop("ocr_nag_at", None)
    ix._pass()
    try:
        while True:
            k, v = app.bgq.get_nowait(); print("bgq", k, flush=True)
    except Exception:
        pass
    os._exit(0)
root.after(2000, step1)
root.after(60000, lambda: os._exit(1))
root.mainloop()
