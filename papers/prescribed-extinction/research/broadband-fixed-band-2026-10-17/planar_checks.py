"""Independent planar checks only; no finite-aperture/3D certification."""
import json
from pathlib import Path
import numpy as np
def matrix_function(A, f):
    values, vectors = np.linalg.eig(A)
    return (vectors * f(values)) @ np.linalg.inv(vectors)
def sqrtm(A):
    return matrix_function(A, np.sqrt)
def expm(A):
    return matrix_function(A, np.exp)
from numpy.polynomial.legendre import leggauss

OUT=Path(__file__).parent
I=np.eye(2,dtype=complex); ey=np.array([0.,1.],complex); Px=np.diag([1.,0.]); Py=I-Px

def slab(eps,k,d):
    n=np.asarray(sqrtm(eps),complex)
    r0=(I-n)@np.linalg.inv(I+n); p=expm(1j*k*d*n)
    den=np.linalg.inv(I-r0@r0@p@p)
    return r0@(I-p@p)@den,(I-r0@r0)@p@den

def scalar(eps,k,d):
    n=np.sqrt(complex(eps)); r0=(1-n)/(1+n); p=np.exp(1j*k*d*n)
    return r0*(1-p*p)/(1-r0*r0*p*p),(1-r0*r0)*p/(1-r0*r0*p*p)

def stack(C,theta,N,w,h,alpha,d):
    D=np.diag([1.,theta]); eps=I+D@C@D/N
    RW,TW=slab(eps,w,d); ra,ta=scalar(1+alpha,w,h)
    RA=ra*Px; TA=ta*Px+np.exp(1j*w*h)*Py
    G=np.linalg.inv(I-RA@RW); H=np.linalg.inv(I-RW@RA)
    tp=TW@G@TA@ey; rp=TA@RW@G@TA@ey
    tm=TA@H@TW@ey; rm=(RW+TW@RA@H@TW)@ey
    v=np.exp(1j*w*(h+d))
    def powers(t,r):
        X=2*np.real(1-t[1]/v); S=np.vdot(r,r).real+np.vdot(t-v*ey,t-v*ey).real
        A=1-np.vdot(r,r).real-np.vdot(t,t).real
        return X,A,S
    return powers(tp,rp),powers(tm,rm),(eps,RW,TW,RA,TA,G,tp,rp)

# Test actual finite damped stack against independent volume absorption quadrature.
C=np.array([[1+.03j,.4],[.4,1.5+.04j]],complex); th=.21; N=5; w=1.3; h=2.; d=3.; alpha=.1+.15j
pp,pm,aux=stack(C,th,N,w,h,alpha,d)
eps,RW,TW,RA,TA,G,tp,rp=aux
nodes,weights=leggauss(240)
def absorb(epsilon,width,E0,H0):
    n=np.asarray(sqrtm(epsilon),complex); ni=np.linalg.inv(n); loss=(epsilon-epsilon.conj().T)/(2j)
    val=0.
    for z,weight in zip((nodes+1)*width/2,weights*width/2):
        # Direct standing-wave propagation, independent of slab power accounting.
        U=expm(1j*w*z*n); V=expm(-1j*w*z*n)
        E=(U+V)@E0/2+(U-V)@ni@H0/2
        val+=weight*w*np.vdot(E,loss@E).real
    return val
EA=I+alpha*Px
ap=absorb(EA,h,ey+rp,ey-rp)
a=G@TA@ey; b=RW@a
ap+=absorb(eps,d,a+b,a-b)
volume={'X_plus':pp[0],'X_minus':pm[0],'A_plus_flux':pp[1],'A_plus_volume':ap,'A_minus_flux':pm[1],
        'energy_residual_plus':abs(pp[0]-pp[1]-pp[2]),'energy_residual_minus':abs(pm[0]-pm[1]-pm[2]),
        'reciprocal_extinction_residual':abs(pp[0]-pm[0]),'volume_absorption_residual':abs(ap-pp[1])}

# Lossless plate unitarity independently checks interface/scattering matrix algebra.
unit=[]
for ww in np.linspace(1,2,31):
    D=np.diag([1.,.2]); R,T=slab(I+D@np.array([[1.,.4],[.4,1.5]])@D/7,ww,3.7)
    unit.append(np.linalg.norm(R.conj().T@R+T.conj().T@T-I))

# Exact finite slab+absorber, increasing weak/thick scale, normalized by theta^2.
tau=2*np.pi/3; c0=np.array([[1.,.4],[.4,1.5]])
conv=[]
for nn in [10,30,100,300]:
    for theta in [.03,.01,.003]:
        errs=[]; gammas=[]; rec=[]
        for ww in np.linspace(1,2,21):
            al=4/(nn*(4-(ww/2)**2-1j*ww/2))
            p,m,_=stack(c0,theta,nn,ww,nn*nn/1.5,al,2*tau*nn)
            target=4*.4**2*np.sin(tau*ww/2)**2
            errs.append(abs(p[0]/theta**2-target))
            gammas.append(abs(p[1]-m[1])/p[0]);rec.append(abs(p[0]-m[0])/theta**2)
        conv.append({'N':nn,'theta':theta,'max_abs_Y_error':max(errs),'min_gamma':min(gammas),'max_normalized_reciprocity_residual':max(rec)})

# Signed rational fit and explicitly PSD-completed Lorentz residues.
ws=np.linspace(1,2,501); target=1/(2*np.sin(tau*ws/2))
poles=np.array([4.5,5.,6.,8.,12.,20.,40.,80.])
V=1/(poles[None,:]-ws[:,None]**2)
scale=np.linalg.norm(V,axis=0); beta=np.linalg.lstsq(V/scale,target,rcond=1e-13)[0]/scale
eta=.00001*(poles-4)/len(poles)
a=1e7/(1e7-ws**2)+(1/(poles[None,:]-ws[:,None]**2))@eta+1e-10/(100-ws**2)
b=V@beta; cc=V@(beta**2/eta)+1e-10/(100-ws**2)
y=4*(b/a)**2*np.sin(tau*ws*a/2)**2
center=np.argmin(abs(ws-1.5)); fixed=4*np.sin(tau*ws/2)**2
res_eigs=[float(np.linalg.eigvalsh(np.array([[e,bb],[bb,bb*bb/e]]))[0]) for e,bb in zip(eta,beta)]
shaping={'band':[1,2],'center':1.5,'target_H':1,'max_b_error':float(max(abs(b-target))),
 'max_a_error':float(max(abs(a-1))),'max_c':float(max(cc)),'min_Y':float(min(y)),'max_Y':float(max(y)),
 'center_Y':float(y[center]),'floor_ratio':float(min(y)/y[center]),'fixed_axes_floor_ratio':float(min(fixed)/fixed[center]),
 'poles_squared':poles.tolist(),'signed_beta':beta.tolist(),'positive_eta':eta.tolist(),
 'residue_psd_note':'Each residue is exactly vv^T with v=(sqrt(eta), beta/sqrt(eta)); floating point eigenvalues are not a PSD certificate.'}
result={'scope':'Planar finite homogeneous layers and ideal theta-Taylor shaping only; no finite 3D/aperture or formal verification.',
 'finite_stack_energy_reciprocity':volume,'max_lossless_plate_unitarity_residual':float(max(unit)),
 'normalized_finite_stack_convergence':conv,'rational_PSD_shaping_ideal_coefficient':shaping}
(OUT/'numerical_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

