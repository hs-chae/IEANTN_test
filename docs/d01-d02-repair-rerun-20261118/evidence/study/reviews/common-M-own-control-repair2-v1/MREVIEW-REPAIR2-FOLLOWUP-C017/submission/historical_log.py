"""Exact older evaluator point-log replay, using its unchanged archive bytes."""
import os,sys,zipfile
f=os.path.join(os.getcwd(),"repair_evaluate.py")
sys.path.insert(0,os.getcwd())
src=zipfile.ZipFile("before_own_repair.zip").read("repair_evaluate.py")
sys.argv=[f,"log","200"]
exec(compile(src,f,"exec"),{"__file__":f,"__name__":"__main__"})
