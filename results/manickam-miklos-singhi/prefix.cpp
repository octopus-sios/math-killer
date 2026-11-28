// Exact box checker; probability arithmetic fixed-point, all prunings one-sided.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <vector>
using I=long long; using Z=__int128_t;
constexpr I Q=10000000,R=1000000;
constexpr int MD=10, M=1<<MD;
I a,b,c,d;int B,D,G,X,N,U,H,J,TR,noTie,coarse;
I ga,de;
std::vector<int>F,LC;
std::vector<I>zl,zh;
I pr[MD+1][M],zs[MD+1][M],ncall=0,nmix=0,nwin=0,ntie=0;
std::array<int,MD>lo_,hi_;
I up(I n,I den){return n<=0?n/den:1+(n-1)/den;}
I root(I x){I l=0,r=R*U+1;while(r-l>1){I m=(r+l)/2;if(m*m<=x)l=m;else r=m;}return l;}
bool load(){
 if(!(std::cin>>a>>b>>c>>d>>B>>D>>G>>U>>H>>J>>TR>>ga>>de>>noTie>>coarse))return false;
 if(!(0<a&&a<=b&&0<c&&c<=d&&b<(1LL<<38)&&d<(1LL<<38)
    &&1<=U&&U<=1024&&1<=B&&B<=512&&1<=D&&D<=512&&1<=G&&G<=16
    &&1<=coarse&&coarse<=U&&1<=H&&H<=MD&&0<ga&&ga<=R&&de>0&&de<=3*R&&J>=0&&J<=1000&&TR>=0&&TR<=Q))return false;
 X=G*D;N=2*X+1; F.resize((B+1)*N);
 for(int j=0;j<=B;j++)for(int i=0;i<N;i++){
 int &v=F[j*N+i];if(!(std::cin>>v)||v<0||v>Q||(i>0&&v>F[j*N+i-1]))return false;}
 zl.resize(U*U+1);zh=zl;for(I i=0;i<=I(U)*U;i++){
 I x=(I(U)*U-i)*R*R;zl[i]=root(x);zh[i]=zl[i]+(zl[i]*zl[i]<x);}
 pr[0][0]=Q; for(int h=1;h<=H;h++)for(int i=0;i<(1<<h);i++)
     pr[h][i]=pr[h-1][i>>1]*(i&1?a:b-a)/b;
 return true;
}
// Returns 1 if box certified or infeasible, 0 if unresolved.
int bound(int h,int l,int u,I sl,I sh,int next=-1) {
 ++ncall; lo_[h-1]=l;hi_[h-1]=u;
 sl+=l*l;sh+=u*u;if(sl>U*U)return 1;
 I zlo=zl[std::min(sh,I(U*U))],zhi=zh[sl];int cap=zlo?int(std::min(I(B),up((next<0?u:next)*R*B,zlo))):B;
 const int*row=F.data()+cap*N;int vals[M];
 I sum=0;int nm=1<<h;
 for(int i=0;i<nm;i++){
 I z=zs[h-1][i>>1]+(i&1?-de*l:ga*u);zs[h][i]=z;
 I k=z<0?(zhi?up(z*D,zhi):-X):(zlo?up(z*D,zlo):X+1);
 int v=k>X?0:row[X+std::max(-I(X),k)]; vals[i]=v;sum+=pr[h][i]*v;
 }
 if(h==1&&J>0&&(Q-vals[1])*1000<=Q*J){nmix++;return 1;}
 if(Z(sum)*d>Z(c)*Q*Q){nwin++;return 1;}
 if(noTie==2){
    int top=nm-1;for(int i=0;i<nm/2;i++){
        int k=top^i;I g=TR-vals[i]-vals[k];
        if(g>0)sum+=g*std::min(pr[h][i],pr[h][k]);
    }
    if(Z(sum)*d>Z(c)*Q*Q){ntie++;return 1;}
 }
 if(!noTie && h>=3){
    // At p<1/3: for a partition of the prefix into three distinct patterns
    // the sum of their standardized thresholds is negative. Consume each
    // mask's lower-bound credit at most once, in a deterministic greedy order.
    bool used[M]={};int top=nm-1;
    for(int i=1;i<nm;i++)if(!used[i]){int rem=top^i;
      for(int j=(rem-1)&rem;j>i;j=(j-1)&rem){int k=rem^j;
        if(k<=j||used[j]||used[k])continue;
        I g=TR-vals[i]-vals[j]-vals[k];if(g<=0)continue;
        sum+=g*std::min(pr[h][i],std::min(pr[h][j],pr[h][k]));
        used[i]=used[j]=used[k]=true;break;
      }
    }
    if(Z(sum)*d>Z(c)*Q*Q){ntie++;return 1;}
 }
 return 0;
}
using Box=std::array<int,MD>;
bool fine(Box low,Box high){
  // Intersect with descending order and the unit sphere. Infeasibility
  // and tightened upper/lower endpoints preserve every actual vector.
  for(int i=H-2;i>=0;i--)low[i]=std::max(low[i],low[i+1]);
  for(int i=1;i<H;i++)high[i]=std::min(high[i],high[i-1]);
  I sl=0,sh=0;int split=-1,score=0;
  for(int i=0;i<H;i++){
    if(low[i]>high[i])return true;
    if(bound(i+1,low[i],high[i],sl,sh,(i+1<H?high[i+1]:-1)))return true;
    int width=high[i]-low[i];if(width>1&&width*(H+1-i)>score){
        score=width*(H+1-i);split=i;
    }
    sl+=low[i]*low[i];sh+=high[i]*high[i];
  }
  if(split<0){std::cout<<"UNRESOLVED ";for(int i=0;i<H;i++)std::cout<<high[i]<<" ";
    std::cout<<" / "<<U<<"\n";return false;}
  int m=(low[split]+high[split])/2;Box h2=high,l2=low;h2[split]=m;l2[split]=m;
  return fine(low,h2)&&fine(l2,high);
}
bool cover(int h,int l,int u,I sl,I sh){
 if(bound(h,l,u,sl,sh))return true;
 if(u-l>coarse){int m=(l+u)/2;return cover(h,l,m,sl,sh)&&cover(h,m,u,sl,sh);}
 if(h==H&&coarse>1){
     Box ll=lo_,hh=hi_;bool ok=fine(ll,hh);
     I s0=0,s1=0;for(int i=0;i<H-1;i++){
        bound(i+1,ll[i],hh[i],s0,s1);
        s0+=ll[i]*ll[i];s1+=hh[i]*hh[i];
     }
     return ok;
 }
 if(h==H){std::cout<<"UNRESOLVED ";for(int i=0;i<h;i++)std::cout<<hi_[i]<<" ";std::cout<<" / "<<U<<"\n";return false;}
 return cover(h+1,0,u,sl+l*l,sh+u*u);
}
int main(){std::ios::sync_with_stdio(false);std::cin.tie(nullptr);
 if(!load()){std::cerr<<"invalid bounds/input\n";return 2;}
 bool ok=cover(1,0,U,0,0);std::cout<<(ok?"PASS ":"FAIL ")<<ncall<<" "<<nmix<<" "<<nwin<<" "<<ntie<<"\n";return ok?0:1;}
