import os, sys, time, base64, io, faulthandler; faulthandler.enable()
sys.path.insert(0, "smart-explorer")
import smart_explorer as S, tkinter as tk
from PIL import ImageGrab
inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
def grab(win, tag, full=False):
    win.update(); time.sleep(0.5); win.update()
    x, y, w, h = win.winfo_rootx(), win.winfo_rooty(), win.winfo_width(), win.winfo_height()
    im = ImageGrab.grab((x, y, x + w, y + (h if full else min(h, 700))))
    b = io.BytesIO(); im.save(b, "PNG")
    print(tag + ":" + base64.b64encode(b.getvalue()).decode(), flush=True)
def go():
    print("go", flush=True)
    dlg = S.SettingsDialog(app); print("dlg ok", flush=True)
    grab(dlg.win, "IMG1", True)
    dlg.builtin_bg("하늘")
    print("bg", S.THEME.get("bg_image"), os.path.exists(S.THEME.get("bg_image", "")), flush=True)
    dlg.ok() if hasattr(dlg, "ok") else None
    root.update(); time.sleep(0.5)
    app.panes[0].preview.clear(); root.update()
    grab(root, "IMG2")
    os._exit(0)
root.after(2500, go)
root.after(60000, lambda: os._exit(1))
root.mainloop()

print("end", flush=True)
