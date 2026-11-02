import sys, os
sys.path.insert(0, "smart-explorer")
import smart_explorer as S, tkinter as tk
r = tk.Tk(); r.title("source"); r.geometry("220x160+800+580"); r.attributes("-topmost", True)
tk.Label(r, text="끌어 갈 파일", bg="#ffe").pack(fill="both", expand=True)
def start(e):
    S.OLE_DND.drag_files(int(r.wm_frame(), 16), [sys.argv[1]])
r.bind("<B1-Motion>", start)
r.mainloop()
