import os, sys, io, base64, time, tempfile
which = sys.argv[1]
def shot(root, name, win):
    from PIL import ImageGrab
    for _ in range(8): root.update(); time.sleep(0.12)
    x, y = win.winfo_rootx(), win.winfo_rooty()
    img = ImageGrab.grab(bbox=(x - 8, y - 32, x + win.winfo_width() + 8, y + min(win.winfo_height(), 420) + 8))
    b = io.BytesIO(); img.save(b, "PNG"); s = base64.b64encode(b.getvalue()).decode()
    for i in range(0, len(s), 4000): print("IMG%s:%s" % (name, s[i:i+4000]), flush=True)
if which == "se":
    sys.path.insert(0, "smart-explorer")
    import smart_explorer as S, tkinter as tk
    inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
    def go():
        app.show_guide()
        w = [c for c in root.winfo_children() if isinstance(c, tk.Toplevel)][-1]
        shot(root, "se", w); os._exit(0)
    root.after(1500, go); root.mainloop()
else:
    sys.path.insert(0, "smart-clipboard")
    import smart_clipboard as S
    S.DATA_DIR = tempfile.mkdtemp()
    app = S.App()
    def go():
        app.show(); app.open_settings()
        shot(app.root, "clip", app._settings_win); os._exit(0)
    app.root.after(1500, go); app.run()
