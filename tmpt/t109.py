import os, sys, time, tempfile, base64, io
sys.path.insert(0, "smart-explorer")
import smart_explorer as S, tkinter as tk
from PIL import ImageGrab
d = tempfile.mkdtemp()
# encrypted PDF
from pypdf import PdfWriter
w = PdfWriter(); w.add_blank_page(300, 400); w.encrypt("1234")
pdfp = os.path.join(d, "비밀.pdf"); w.write(pdfp)
# encrypted xlsx
import openpyxl, msoffcrypto
wb = openpyxl.Workbook(); ws = wb.active; ws["A1"] = "예산"; ws["B2"] = "1,000원"
plain = os.path.join(d, "plain.xlsx"); wb.save(plain)
xp = os.path.join(d, "급여.xlsx")
with open(plain, "rb") as f, open(xp, "wb") as o:
    msoffcrypto.format.ooxml.OOXMLFile(f).encrypt("abcd", o)
os.remove(plain)
print("kinds", S.locked_kind(pdfp, ".pdf"), S.locked_kind(xp, ".xlsx"), flush=True)
inst = S.SingleInstance(); root = tk.Tk(); app = S.App(root, inst)
def grab(tag):
    root.update(); time.sleep(0.4); root.update()
    pv = app.panes[0].preview
    x, y, w_, h = pv.winfo_rootx(), pv.winfo_rooty(), pv.winfo_width(), pv.winfo_height()
    im = ImageGrab.grab((x, y, x + w_, y + min(h, 420)))
    b = io.BytesIO(); im.save(b, "PNG")
    print(tag + ":" + base64.b64encode(b.getvalue()).decode(), flush=True)
def step():
    pv = app.panes[0].preview
    pv.show(xp, [], None, True); grab("IMG1")
    pv.pw_var.set("wrong"); pv._unlock(); print("wrong ->", pv.lock_msg.cget("text"), flush=True)
    pv.pw_var.set("abcd"); print("right ->", pv._unlock(), flush=True); grab("IMG2")
    pv.show(pdfp, [], None, True); pv.pw_var.set("1234"); print("pdf ->", pv._unlock(), flush=True); grab("IMG3")
    pv.clear(); pv.show(xp, [], None, True); print("remembered", pv.lock_frame.winfo_ismapped() == 0, flush=True)
    pv.clear(); print("tmp left", os.listdir(os.path.join(S.TMP_DIR, "unlocked")) if os.path.isdir(os.path.join(S.TMP_DIR, "unlocked")) else [], flush=True)
    os._exit(0)
root.after(2500, step)
root.after(60000, lambda: os._exit(1))
root.mainloop()
