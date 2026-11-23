// Erdos #128: for each MTF graph (multicode on stdin) compute min edges over induced k-subsets, k=floor(n/2).
// Counterexample iff 50*min > n^2. Heuristic upper bound first; exact B&B if heuristic >= TH.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint32_t u32;
static int n,k; static u32 adj[32];
static int pc(u32 x){return __builtin_popcount(x);}
static int edges(u32 S){int e=0;for(u32 t=S;t;t&=t-1){int v=__builtin_ctz(t);e+=pc(adj[v]&S);}return e/2;}
static int best;
static void bb(u32 S,int sz,int e,int from){ // choose vertices in increasing order
  if(e>=best) return;
  if(sz==k){best=e;return;}
  if(n-from < k-sz) return;
  // lower bound: each further vertex adds >=0 edges; crude
  for(int v=from; v<=n-(k-sz); v++){
    int ne=e+pc(adj[v]&S);
    if(ne<best) bb(S|(1u<<v),sz+1,ne,v+1);
  }
}
static int TH;
static int heur(void){
  int bestv=1<<30;
  for(int s=0;s<n;s++){
    u32 S=1u<<s; int sz=1,e=0;
    while(sz<k){int bv=-1,bc=1<<30;
      for(int v=0;v<n;v++) if(!(S>>v&1)){int c=pc(adj[v]&S)*64+pc(adj[v]); if(c<bc){bc=c;bv=v;}}
      e+=pc(adj[bv]&S); S|=1u<<bv; sz++;}
    // 1-swap local search
    int imp=1; while(imp){imp=0;
      for(u32 t=S;t&&!imp;t&=t-1){int u=__builtin_ctz(t); int du=pc(adj[u]&S);
        for(int v=0;v<n;v++) if(!(S>>v&1)){int dv=pc(adj[v]&(S&~(1u<<u))); if(dv<du){S=(S&~(1u<<u))|(1u<<v); e=e-du+dv; imp=1; break;}}}}
    if(e<bestv) bestv=e;
    if(bestv<TH) break;
  }
  return bestv;
}
int main(int argc,char**argv){
  TH=atoi(argv[1]); // run exact if heuristic >= TH
  long cnt=0,nex=0; int maxh=-1,maxex=-1; long cex=0;
  int c;
  while((c=getchar())!=EOF){
    n=c; k=n/2; for(int i=0;i<n;i++)adj[i]=0;
    int i=0; int remaining=n-1;
    while(remaining>0){int x=getchar(); if(x==0){i++;remaining--;continue;} adj[i]|=1u<<(x-1); adj[x-1]|=1u<<i;}
    cnt++;
    int h=heur(); if(h>maxh)maxh=h;
    if(h>=TH || 50*h>n*n){ best=h; bb(0,0,0,0); nex++; if(best>maxex)maxex=best;
      if(50*best>n*n){cex++; printf("COUNTEREXAMPLE n=%d min=%d\n",n,best); for(int a=0;a<n;a++)printf("%08x ",adj[a]); printf("\n");}}
  }
  printf("n=%d graphs=%ld maxHeur=%d exactRuns=%ld maxExact=%d bound(n^2/50)=%.2f counterexamples=%ld\n",n,cnt,maxh,nex,maxex,n*n/50.0,cex);
  return 0;
}
