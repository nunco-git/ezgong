import os, sys, time, io, base64
sys.path.insert(0, "smart-explorer")
import smart_explorer as S, tkinter as tk
inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
res = []
def check(c, n): res.append(("OK  " if c else "FAIL") + " " + n); print(res[-1], flush=True)
def pump(t):
    e = time.time() + t
    while time.time() < e: root.update(); time.sleep(0.02)
def shot(name, w=None):
    from PIL import ImageGrab
    pump(0.8)
    w = w or root
    x, y = w.winfo_rootx(), w.winfo_rooty()
    img = ImageGrab.grab(bbox=(x - 8, y - 32, x + w.winfo_width() + 8, y + min(w.winfo_height(), 520) + 8))
    b = io.BytesIO(); img.save(b, "PNG"); s = base64.b64encode(b.getvalue()).decode()
    for i in range(0, len(s), 4000): print("IMG%s:%s" % (name, s[i:i+4000]), flush=True)
def go():
    try:
        check(S.hotkey_text(app.hotkey) == "Ctrl+Shift+E", "기본 단축키 %s" % S.hotkey_text(app.hotkey))
        app.s["zoomed"] = True
        root.withdraw(); pump(0.5)
        app.show_window(); pump(1)
        check(root.state() == "zoomed", "트레이에서 불러오면 전체 화면 (%s)" % root.state())
        d = S.SettingsDialog(app); pump(1)
        check(d.sc_frame.winfo_ismapped() and d.sc_desk.winfo_ismapped(), "환경설정 맨 위 바로가기 칸")
        shot("settings", d.win)
        d.make_desk(); pump(3)
        check(S.has_desktop_shortcut(), "바탕화면 바로가기 만들어짐")
        check(not d.sc_desk.winfo_ismapped(), "만든 뒤 바탕화면 버튼 숨김")
        d.cancel() if hasattr(d, "cancel") else d.win.destroy(); pump(0.3)
        app.show_guide(); pump(1)
        g = [w for w in root.winfo_children() if isinstance(w, tk.Toplevel)][-1]
        shot("guide", g)
    except Exception:
        import traceback; traceback.print_exc()
    print("\n".join(res), flush=True); os._exit(0)
root.after(1500, go); root.mainloop()
