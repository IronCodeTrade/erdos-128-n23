import sys,itertools,subprocess
for n in range(5,15):
    data=subprocess.run(['triangleramsey-1.1/triangleramsey',str(n)],capture_output=True).stdout
    i=0;cnt=0;worst=-1
    while i<len(data):
        N=data[i];i+=1;adj=[0]*N;v=0
        while v<N-1:
            x=data[i];i+=1
            if x==0: v+=1;continue
            adj[v]|=1<<(x-1);adj[x-1]|=1<<v
        assert all(not(adj[a]&adj[b]) for a in range(N) for b in range(N) if adj[a]>>b&1)
        k=N//2;best=10**9
        for S in itertools.combinations(range(N),k):
            m=0
            for s in S: m|=1<<s
            e=sum(bin(adj[s]&m).count('1') for s in S)//2
            if e<best: best=e
        worst=max(worst,best);cnt+=1
    print(n,cnt,'max_min',worst,'bound',n*n/50,'counterexample' if 50*worst>n*n else 'none',flush=True)
