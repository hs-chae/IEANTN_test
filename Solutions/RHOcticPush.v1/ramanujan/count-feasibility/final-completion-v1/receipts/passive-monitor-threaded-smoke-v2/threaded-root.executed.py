import subprocess,threading,time,json,sys
pids=[]
lock=threading.Lock()
def worker():
 p=subprocess.Popen([sys.executable,"-c","import time; x=bytearray(32*1024*1024); time.sleep(4)"])
 with lock:pids.append(p.pid)
 p.wait()
threads=[threading.Thread(target=worker) for _ in range(2)]
for t in threads:t.start()
while len(pids)<2:time.sleep(0.01)
print(json.dumps(pids),flush=True)
for t in threads:t.join()
