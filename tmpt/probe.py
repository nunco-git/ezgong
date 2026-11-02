import sys, os
print("py", sys.version)
import pythoncom, win32con
from win32com.shell import shell, shellcon
print("SHDoDragDrop", hasattr(shell, "SHDoDragDrop"))
print("IID_IDropTargetHelper", hasattr(shell, "IID_IDropTargetHelper"), "CLSID_DragDropHelper", hasattr(shell, "CLSID_DragDropHelper"))
print("RegisterDragDrop", hasattr(pythoncom, "RegisterDragDrop"), "DoDragDrop", hasattr(pythoncom, "DoDragDrop"))
print("IID_IDropTarget", hasattr(pythoncom, "IID_IDropTarget"))
print("IContextMenu", hasattr(shell, "IID_IContextMenu"))
pythoncom.OleInitialize()
try:
    h = pythoncom.CoCreateInstance(shell.CLSID_DragDropHelper, None, pythoncom.CLSCTX_INPROC_SERVER, shell.IID_IDropTargetHelper)
    print("DropTargetHelper ok", h)
except Exception as e:
    print("DropTargetHelper fail", e)
import tempfile
d = tempfile.mkdtemp(); fs = []
for i in range(2):
    p = os.path.join(d, "x%d.txt" % i); open(p, "w").write("x"); fs.append(p)
desk = shell.SHGetDesktopFolder()
eaten, pidl, attr = desk.ParseDisplayName(0, None, d)
folder = desk.BindToObject(pidl, None, shell.IID_IShellFolder)
kids = [folder.ParseDisplayName(0, None, os.path.basename(f))[1] for f in fs]
do = folder.GetUIObjectOf(0, kids, pythoncom.IID_IDataObject, 0)
print("dataobj", do)
cm = folder.GetUIObjectOf(0, kids, shell.IID_IContextMenu, 0)
print("contextmenu", cm)
