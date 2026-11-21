import pathlib,runpy,sys,types
F=pathlib.Path(sys.argv[1]);N=pathlib.Path(sys.argv[2]);name=sys.argv[3]
m=types.ModuleType("ram_cert");m.__file__=str(F/"ram_cert.py")
s=(F/"ram_cert.py").read_text().replace("/ieantn/IEANTN/Nodes/Buthe/v1/Tables.lean",str(N/"IEANTN/Nodes/Buthe/v1/Tables.lean"))
exec(compile(s,m.__file__,"exec"),m.__dict__);sys.modules["ram_cert"]=m
sys.argv=[str(F/(name+".py"))]
s=(F/(name+".py")).read_text().replace("/ieantn/IEANTN/Nodes/Buthe/v1/Tables.lean",str(N/"IEANTN/Nodes/Buthe/v1/Tables.lean"))
exec(compile(s,sys.argv[0],"exec"),{"__name__":"__main__","__file__":sys.argv[0]})
