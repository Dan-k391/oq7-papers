import numpy as np
import json, hashlib
from pathlib import Path

def slab(eps, length):
    n = np.sqrt(complex(eps))
    rho = (1-n)/(1+n)
    phase = np.exp(1j*n*length)
    return rho*(1-phase**2)/(1-rho**2*phase**2), (1-rho**2)*phase/(1-rho**2*phase**2)

def boundary_solve(eta, h, pj, delta, d, theta, side):
    # Independent tangential E/H interface solve, with decaying propagation factors.
    s,c=np.sin(theta),np.cos(theta)
    VA=np.eye(2,dtype=complex); VW=np.array([[c,-s],[s,c]],complex)
    NA=np.diag([np.sqrt(1+1j*eta),1]); NW=np.diag([np.sqrt(pj+1j*delta),1])
    PA=np.diag(np.exp(1j*np.diag(NA)*h)); PW=np.diag(np.exp(1j*np.diag(NW)*d))
    I=np.eye(2); Z=np.zeros((2,2)); ey=np.array([0,1],complex)
    il=ey if side=='+' else np.zeros(2); ir=ey if side=='-' else np.zeros(2)
    mat=np.block([[I,-VA,-VA@PA,Z,Z,Z],[-I,-VA@NA,VA@NA@PA,Z,Z,Z],
                  [Z,VA@PA,VA,-VW,-VW@PW,Z],[Z,VA@NA@PA,-VA@NA,-VW@NW,VW@NW@PW,Z],
                  [Z,Z,Z,VW@PW,VW,-I],[Z,Z,Z,VW@NW@PW,-VW@NW,-I]])
    rhs=np.concatenate([-il,-il,np.zeros(4),ir,-ir])
    sol=np.linalg.solve(mat,rhs).reshape(6,2)
    rl,aa,ba,aw,bw,tr=sol
    reflection=rl if side=='+' else tr; transmission=tr if side=='+' else rl
    X=2*(1-(transmission[1]*np.exp(-1j*(h+d))).real)
    S=np.vdot(reflection,reflection).real+np.vdot(transmission-np.exp(1j*(h+d))*ey,transmission-np.exp(1j*(h+d))*ey).real
    def flux(V,N,P,a,b):
        el=V@(a+P@b); hl=V@N@(a-P@b)
        er=V@(P@a+b); hr=V@N@(P@a-b)
        return (np.vdot(el,hl)-np.vdot(er,hr)).real
    A=flux(VA,NA,PA,aa,ba)+flux(VW,NW,PW,aw,bw)
    outgoing = np.concatenate([rl,tr-np.exp(1j*(h+d))*ey]) if side=='+' else np.concatenate([rl-np.exp(1j*(h+d))*ey,tr])
    return np.array([X,A,S]), outgoing/s

def normalized_formula(eta,h,pj,delta,d,theta):
    s,c=np.sin(theta),np.cos(theta)
    ra,ta=slab(1+1j*eta,h); rw,tw=slab(pj+1j*delta,d)
    va,vw=np.exp(1j*h),np.exp(1j*d); diff=tw-vw; D=1-ra*rw*c*c
    y=2*((1-tw/vw)/D).real
    bp=np.array([rw*va*ta*c/D,rw*va*va*s/D,c*va*(diff+vw*ra*rw)/D,s*va*diff/D])
    bm=np.array([c*ta*diff/D,s*va*diff/D,c*(ra*diff*(vw+diff*c*c)/D+rw),s*(ra*diff**2*c*c/D+rw)])
    cp=np.vdot(bp,bp).real; cm=np.vdot(bm,bm).real
    return y,np.array([y,y-cp,cp]),np.array([y,y-cm,cm]),bp,bm

rng=np.random.default_rng(704231)
err=0.; amp_err=0.; closure=0.; reciprocity=0.
for case in range(200):
    eta=10**rng.uniform(-2,0); h=rng.uniform(.3,30)
    j=int(rng.integers(1,8)); pj=(2*j/(2*j-1))**2; d=(2*j-1)*np.pi
    delta=0. if case%4==0 else 10**rng.uniform(-6,-.3)
    theta=rng.uniform(.02,.9)
    y,fp,fm,bp,bm=normalized_formula(eta,h,pj,delta,d,theta)
    xp,ap=boundary_solve(eta,h,pj,delta,d,theta,'+')
    xm,am=boundary_solve(eta,h,pj,delta,d,theta,'-')
    err=max(err,np.max(np.abs(xp/np.sin(theta)**2-fp)),np.max(np.abs(xm/np.sin(theta)**2-fm)))
    amp_err=max(amp_err,np.max(np.abs(ap-bp)),np.max(np.abs(am-bm)))
    closure=max(closure,abs(xp[0]-xp[1]-xp[2]),abs(xm[0]-xm[1]-xm[2]))
    reciprocity=max(reciprocity,abs(xp[0]-xm[0]))

rows=[]
for n in [5,10,20,40,80]:
    y,fp,fm,*_=normalized_formula(1/n,n*n,4,1e-6,np.pi,0)
    rows.append(dict(n=n,Y=y,Gamma=abs(fp[1]-fm[1])/y))

# Direct zero-angle auxiliary volume equation, midpoint Nyström (diagnostic only).
ny=[]
eta,h,pj,delta,d=.8,2*np.pi,4,.02,np.pi
y,fp,fm,*_=normalized_formula(eta,h,pj,delta,d,0)
for count in [80,160,320]:
    za=(np.arange(count)+.5)*h/count
    zw=h+(np.arange(count//2)+.5)*d/(count//2)
    z=np.concatenate([za,zw]); weights=np.concatenate([np.full(count,h/count),np.full(count//2,d/(count//2))])
    alpha=np.concatenate([np.full(count,1j*eta),np.full(count//2,pj-1+1j*delta)])
    B=.5j*np.exp(1j*np.abs(z[:,None]-z[None,:]))*weights[None,:]
    operator=np.diag(1/alpha)-B
    g=np.zeros((len(z),2),complex); g[count:,0]=np.exp(1j*zw); g[count:,1]=np.exp(-1j*zw)
    response=np.linalg.solve(operator,g)
    Y=np.imag(np.sum(weights[:,None]*np.conj(g)*response,axis=0))
    A=np.sum(weights[:,None]*(-np.imag(1/alpha))[:,None]*abs(response)**2,axis=0)
    ny.append(dict(points=len(z),Y=Y.tolist(),A=A.tolist(),Gamma=float(abs(A[0]-A[1])/Y[0])))

summary=dict(seed=704231,random_cases=200,max_normalized_power_error=err,max_normalized_amplitude_error=amp_err,max_flux_closure_error=closure,max_extinction_reciprocity_error=reciprocity,table_1=rows,zero_angle_volume_diagnostic=ny,zero_angle_exact=dict(Y=y,Aplus=fp[1],Aminus=fm[1],Gamma=abs(fp[1]-fm[1])/y),limitations='No finite-aperture continuum simulation; floating-point and midpoint diagnostics are not proofs.')
assert err<1e-9 and amp_err<1e-10 and closure<1e-11 and reciprocity<1e-11
Path('work/independent_checks.json').write_text(json.dumps(summary,indent=2),encoding='utf-8')
print(json.dumps(summary,indent=2))
