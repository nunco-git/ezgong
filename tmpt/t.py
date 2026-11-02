import os, sys, time, ctypes, importlib, threading
sys.path.insert(0, os.path.join(os.getcwd(), "smart-explorer")); sys.path.insert(0, os.path.join(os.getcwd(), "tmpt"))
mod = sys.argv[1]
S = importlib.import_module(mod)
import tkinter as tk
u = ctypes.windll.user32
def click(x, y):
    u.SetCursorPos(int(x), int(y)); time.sleep(0.15)
    u.mouse_event(2, 0, 0, 0, 0); time.sleep(0.05); u.mouse_event(4, 0, 0, 0, 0)
inst = S.SingleInstance()
root = tk.Tk()
app = S.App(root, inst)
res = {}
def pump(sec):
    end = time.time() + sec
    while time.time() < end:
        root.update(); time.sleep(0.02)
def step():
    dlg = S.AlarmDialog(app)
    pump(0.8)
    dlg.test(); pump(1.2)
    pops = [w for w in root.winfo_children() if isinstance(w, tk.Toplevel) and w.title() == "스마트탐색기 알람"]
    p = pops[-1]
    btn = [c for c in p.winfo_children()[0].winfo_children()[-1].winfo_children() if c.cget("text") == "확인"][0]
    x = btn.winfo_rootx() + btn.winfo_width() // 2; y = btn.winfo_rooty() + btn.winfo_height() // 2
    click(x, y); pump(1.0)
    res["ok_closes"] = not p.winfo_exists()
    # 다시: X(닫기) 대신 WM_CLOSE 메시지
    dlg.test(); pump(1.2)
    pops = [w for w in root.winfo_children() if isinstance(w, tk.Toplevel) and w.title() == "스마트탐색기 알람" and w.winfo_exists()]
    p = pops[-1]
    hwnd = int(p.wm_frame(), 16)
    u.PostMessageW(hwnd, 0x0010, 0, 0); pump(1.0)
    res["x_closes"] = not p.winfo_exists()
    res["dialog_grab_back"] = str(root.grab_current()) == str(dlg.win) if root.grab_current() else False
    print(mod, res, flush=True)
    os._exit(0)
root.after(1500, step)
root.mainloop()
