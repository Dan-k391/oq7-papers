"""Independent adversarial OQ7 checks; no author's implementation imported.

Run with Python 3.12+, numpy, scipy, sympy and mpmath. Outputs are finite
models or symbolic identities, never a certificate of continuum convergence.
"""
from __future__ import annotations
import os
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
import json
import sys
from pathlib import Path
import numpy as np
import scipy
import scipy.linalg as la
import sympy as sp
import mpmath as mp

HERE = Path(__file__).resolve().parent


def symbolic_checks():
    rho, c = sp.symbols("rho c", real=True)
    D = 2-rho*c-c*c
    lam = c*(rho-c)/D
    s = sp.sqrt(1-c*c)
    Z = sp.Matrix([[(rho+c)/4, -s/(2*(1+lam))],
                   [-s/(2*(1+lam)), (rho-c)/(4*lam)]])
    W = sp.Matrix([[(rho+c)/2, -s/2],[-s/2,(rho-c)/2]])
    B = sp.diag(1,lam)
    # E in the eigenbasis of B0, from a direct rotation of the off-diagonal form.
    E = sp.Matrix([[s/2,c/2],[c/2,-s/2]])
    nu = -s/((1+lam)*c)
    checks = {
        "middle_certificate_sylvester": B*Z+Z*B-W,
        "middle_determinant": sp.det(Z)-D*(rho-c)/(16*c*(1-c*c)),
        "middle_support_lower_right": (Z-nu*E)[1,1],
        "middle_support_offdiagonal": (Z-nu*E)[0,1],
        "middle_support_identity": (Z-nu*E)*(sp.eye(2)-B*B),
        "middle_lambda_identity": (rho-c)*(1+lam)*c-2*lam*(1-c*c),
    }
    r=(rho+c-2*rho*c*c)/D
    checks["middle_r_derivative"] = sp.diff(r,c)-(2+rho*rho-6*rho*c+(1+2*rho*rho)*c*c)/(D*D)
    B0=sp.Matrix([[139,17*sp.sqrt(21)],[17*sp.sqrt(21),71]])/190
    Z0=sp.Matrix([[sp.Rational(7,8),-17*sp.sqrt(21)/168],[-17*sp.sqrt(21)/168,sp.Rational(3,8)]])
    W0=sp.diag(sp.Rational(9,10),-sp.Rational(1,10))
    E0=sp.Matrix([[0,sp.Rational(1,2)],[sp.Rational(1,2),0]])
    nu0=-19*sp.sqrt(21)/42
    checks.update({
        "rational_sylvester": B0*Z0+Z0*B0-W0,
        "rational_det_Z": sp.det(Z0)-sp.Rational(19,168),
        "rational_support": (Z0-nu0*E0)*(sp.eye(2)-B0*B0),
        "rational_r": sp.trace(W0*B0)-sp.Rational(59,95),
        "rational_delta": sp.Rational(6,5)*(B0*B0)[0,1]-1071*sp.sqrt(21)/9025,
        "rational_eigen_polynomial": sp.det(B0-sp.symbols("x")*sp.eye(2))-(1-sp.symbols("x"))*(sp.Rational(2,19)-sp.symbols("x")),
    })
    result={}
    for name,val in checks.items():
        if isinstance(val,sp.MatrixBase):
            simplified=val.applyfunc(sp.simplify)
            ok=all(x==0 for x in simplified)
        else:
            simplified=sp.simplify(val)
            ok=simplified==0
        result[name]={"is_zero":bool(ok),"exact_remainder":str(simplified)}
        assert ok, (name,simplified)
    result["rational_delta_decimal"]=str(sp.N(1071*sp.sqrt(21)/9025,45))
    # Cubic centered-insertion expansion: independently multiply finite Taylor series.
    P,Q,x=sp.symbols("P Q x",real=True)
    A=sp.I*sp.Matrix([[0,1],[P,0]])
    BB=sp.Matrix([[0,0],[-Q,0]])
    def series(M):
        return sum((M**j*x**j/sp.factorial(j) for j in range(5)),sp.zeros(2))
    prod=series(-A/2)*series(A+BB)*series(-A/2)
    cubic=prod.applyfunc(lambda e:sp.expand(e).coeff(x,3))
    C3=sp.Matrix([[0,-Q],[Q*(P+2*sp.I*Q),0]])/12
    assert cubic.applyfunc(sp.simplify)==C3
    result["centered_insertion_cubic"]={"exact_matrix":str(cubic),"matches_paper":True}
    return result


def envelope(rho,r):
    d=np.sqrt(1-rho*rho)
    if r<=rho/2: return d
    if r>=rho: return 1-r*r
    c=2*(2*r-rho)/(1+rho*r+np.sqrt((1+rho*r)**2-4*(2*rho-r)*(2*r-rho)))
    lam=c*(rho-c)/(2-rho*c-c*c)
    return d*(1-lam*lam)*np.sqrt(1-c*c)


def contraction_search(count=12000):
    rng=np.random.default_rng(7462026)
    worst=-1.0
    worst_record=None
    for idx in range(count):
        n=2+(idx%5)
        U,_=np.linalg.qr(rng.standard_normal((n,n))+1j*rng.standard_normal((n,n)))
        singular=rng.random(n)
        # Include singular, unitary, and almost-saturated singular values explicitly.
        if idx%7==0: singular[0]=1
        if idx%11==0: singular[-1]=0
        if idx%17==0: singular[:]=1
        S=(U*singular)@U.T
        rho=[0.000001,0.05,0.4,0.8,0.999999][idx%5]
        u=np.zeros(n,dtype=complex)
        u[0]=np.sqrt((1+rho)/2)
        u[1]=1j*np.sqrt((1-rho)/2)
        v=u.conj()
        z=np.vdot(u,S@u)
        r=abs(z.real)
        delta=abs(np.vdot(S@u,S@u).real-np.vdot(S@v,S@v).real)
        bound=envelope(rho,r)
        difference=delta-bound
        if difference>worst:
            worst=difference
            worst_record={"sample":idx,"dimension":n,"rho":rho,"r":float(r),"delta":float(delta),"bound":float(bound)}
        assert difference<1e-11,(idx,difference)
    return {"samples":count,"seed":7462026,"largest_delta_minus_bound":float(worst),"closest_sample":worst_record,"claim":"Finite floating-point falsification search only."}


def grazing_check():
    """Truncated integrals expose a logarithmic square-norm divergence.

    The test uses the leading exact TE singularity for k=L=1 and Gaussian
    weight exp(-rho^2/2). The accompanying audit gives a compact smooth-source
    analytic counterexample to a stronger global L2 claim, absent in the paper.
    """
    mp.mp.dps=80
    eps_list=[mp.mpf(10)**(-p) for p in (2,4,6,8,10,12)]
    rows=[]
    for eps in eps_list:
        low=mp.mpf("0.5"); high=mp.mpf("1.5")
        # t=rho^2 regularizes the scalar radial integration; beta=|1-t|^1/2.
        def l1(t): return mp.pi*mp.exp(-t/2)/(2*mp.sqrt(abs(1-t)))
        def l2(t): return mp.pi*mp.exp(-t)/(4*abs(1-t))
        val1=mp.quad(l1,[low**2,1-eps])+mp.quad(l1,[1+eps,high**2])
        val2=mp.quad(l2,[low**2,1-eps])+mp.quad(l2,[1+eps,high**2])
        rows.append({"grazing_excision_in_rho_squared":str(eps),"weighted_L1":str(val1),"weighted_squared_L2":str(val2)})
    slope=(mp.mpf(rows[-1]["weighted_squared_L2"])-mp.mpf(rows[-2]["weighted_squared_L2"]))/mp.log(eps_list[-2]/eps_list[-1])
    return {"precision_digits":80,"model":"Exact leading TE singularity, k=L=1, Gaussian frequency weight; truncated integrals.","rows":rows,"observed_log_slope":str(slope),"exact_asymptotic_log_slope":str(mp.pi/(2*mp.e)),"stronger_global_L2_claim":"False analytically, as proved separately in the audit; not a claim of Paper B."}


def grazing_operator_lower_bound():
    """Integrate only a known positive grazing patch of the radiation identity.

    For k=L=1 and P_R=e_y exp(i x) on a side-R square, its radiation quadratic
    form divided by ||P_R||^2 is a lower bound on ||T_R||.  With n_y=v/R and
    n_z=w/sqrt(R), a fixed (v,w) patch has solid angle O(R^-3/2).
    """
    gg,ww=np.polynomial.legendre.leggauss(60)
    a=.2
    vv,zz=np.meshgrid(a*gg,a*gg,indexing="ij")
    weight=(a*a)*ww[:,None]*ww[None,:]
    rows=[]
    for R in [1.,4.,16.,64.,256.,1024.]:
        ny=vv/R;nz=zz/np.sqrt(R);nx=np.sqrt(1-ny*ny-nz*nz)
        # np.sinc(y)=sin(pi y)/(pi y).
        ft=(R*R)*np.sinc(R*(nx-1)/(2*np.pi))*np.sinc(R*ny/(2*np.pi))*np.sinc(nz/(2*np.pi))
        sphere_patch=np.sum(weight*(1-ny*ny)*abs(ft)**2/(R**1.5*nx))
        rayleigh=sphere_patch/(16*np.pi*np.pi*R*R)
        rows.append({"R":R,"positive_patch_Rayleigh_lower_bound":float(rayleigh),"lower_bound_divided_by_sqrt_R":float(rayleigh/np.sqrt(R))})
    return {"k":1,"L":1,"patch_halfwidth":a,"rows":rows,"claim":"Exact finite-source radiation integrand evaluated numerically on a positive patch; the analytic sqrt(R) lower bound is proved in the audit. Paper B does not claim ||T_R|| is uniform."}


def slab_coeff(n,h,k):
    r0=(1-n)/(1+n)
    p=np.exp(1j*n*k*h)
    den=1-r0*r0*p*p
    return r0*(1-p*p)/den,(1-r0*r0)*p/den


def planar_stable(t,eta,delta,h,d,k=2*np.pi,j=1):
    s=np.sqrt(1-t*t)
    V=np.array([[-t,s],[s,t]])
    pj=(2*j/(2*j-1))**2
    epsA=np.diag([1+1j*(eta+delta),1+1j*delta])
    epsW=((pj+1)*np.eye(2)-(pj-1)*V)/2+1j*delta*np.eye(2)
    eig,O=np.linalg.eigh(epsW.real)
    rA,tA=zip(*(slab_coeff(np.sqrt(epsA[ii,ii]),h,k) for ii in range(2)))
    rW,tW=zip(*(slab_coeff(np.sqrt(e+1j*delta),d,k) for e in eig))
    R1=np.diag(rA); T1=np.diag(tA)
    R2=(O*np.array(rW))@O.T; T2=(O*np.array(tW))@O.T
    U=la.solve(np.eye(2)-R1@R2,T1)
    VV=la.solve(np.eye(2)-R2@R1,T2)
    Rleft=R1+T1@R2@U; Tleft=T2@U
    Rright=R2+T2@R1@VV; Tright=T1@VV
    e=np.array([0.,1.])
    def obs(R,T):
        outR=R@e; outT=T@e
        A=1-np.vdot(outR,outR).real-np.vdot(outT,outT).real
        normT=np.exp(-1j*k*(h+d))*outT
        X=2*(1-np.vdot(e,normT).real)
        C=np.vdot(outR,outR).real+np.vdot(normT-e,normT-e).real
        return {"A":float(A),"X":float(X),"C":float(C)}
    op=obs(Rleft,Tleft); om=obs(Rright,Tright)
    return {"plus":op,"minus":om,"Gamma":abs(op["A"]-om["A"])/op["X"]},epsA,epsW


def planar_exponential(epsA,epsW,h,d,k=2*np.pi):
    I=np.eye(2); Z=np.zeros((2,2))
    def layer(eps,ll):
        return la.expm(k*ll*np.block([[Z,I],[-eps,Z]]))
    F=layer(epsW,d)@layer(epsA,h)
    Wp=np.vstack([I,1j*I]); Wm=np.vstack([I,-1j*I])
    M=np.column_stack([-F@Wm,Wp])
    # Two independent left and two right incidences in one 4x4 solve.
    sol=la.solve(M,np.column_stack([F@Wp,-Wm]))
    rL=sol[:2,:2]; tL=sol[2:,:2]
    tR=sol[:2,2:]; rR=sol[2:,2:]
    e=np.array([0.,1.])
    def obs(R,T):
        rr=R@e;tt=T@e
        A=1-np.vdot(rr,rr).real-np.vdot(tt,tt).real
        nt=np.exp(-1j*k*(h+d))*tt
        X=2*(1-np.vdot(e,nt).real)
        C=np.vdot(rr,rr).real+np.vdot(nt-e,nt-e).real
        return {"A":float(A),"X":float(X),"C":float(C)}
    p=obs(rL,tL);m=obs(rR,tR)
    return {"plus":p,"minus":m,"Gamma":abs(p["A"]-m["A"])/p["X"]}


def planar_checks():
    records=[]
    for name,t,eta,delta,h in [("A",.7,.8,.002,1.),("B",.9,.3,5e-5,2.)]:
        stable,eA,eW=planar_stable(t,eta,delta,h,.5)
        exponential=planar_exponential(eA,eW,h,.5)
        error=max(abs(stable[sign][ob]-exponential[sign][ob]) for sign in ("plus","minus") for ob in ("A","X","C"))
        records.append({"set":name,"stable":stable,"independent_exponential":exponential,"maximum_power_discrepancy":error})
        assert error<1e-10
    limiting=[]
    for m in [4,10,20,50,100]:
        # Recalculate using independent stable composition; k=1 for dimensionless kh.
        v,_,_=planar_stable(1-1/m,1/m,m**-6,m*m,np.pi,k=1)
        limiting.append({"m":m,"delta":m**-6,"Gamma":v["Gamma"],"plus":v["plus"],"minus":v["minus"]})
    v,_,_=planar_stable(.99,.01,1e-12,10000,201*np.pi,k=1,j=101)
    return {"sets":records,"limiting_sequence":limiting,"cap_P_1_01_m100_j101":v,"claim":"Exact planar formulas, evaluated numerically. Finite-precision equality is not proof."}


def thickness_benchmark():
    mp.mp.dps=80
    P=mp.mpf(4);Q=mp.mpf(2);g0=mp.mpf(1)
    A=mp.j*mp.matrix([[0,1],[P,0]])
    B=mp.matrix([[0,0],[-Q,0]])
    W=mp.matrix([[1,1],[1,-1]])
    Sigma=mp.matrix([[0,1],[1,0]])
    targetT=mp.mpf(12)/25;targeta=mp.mpf(8)/25
    rows=[]
    for m in [4,8,16,32,64,128]:
        xi=g0/(Q*m)
        D=mp.expm(-A*xi/2)*mp.expm((A+B)*xi)*mp.expm(-A*xi/2)
        F=D**m
        def Lam(l): return mp.matrix([[mp.exp(l),0],[0,mp.exp(-l)]])
        def response(lL,lR,full=False):
            FF=Lam(lR)*F*Lam(lL)
            K=W**-1*FF*W
            rL=-K[1,0]/K[1,1];rR=K[0,1]/K[1,1];t=1/K[1,1]
            T=abs(t)**2;a=1-T-(abs(rL)**2+abs(rR)**2)/2
            if full:return T,a,abs(abs(rR)**2-abs(rL)**2),FF
            return T-targetT,a-targeta
        ll,lr=mp.findroot(response,(-mp.log(3)/2,0),tol=mp.mpf("1e-65"))
        T,a,contrast,FF=response(ll,lr,True)
        defect=Sigma-FF.H*Sigma*FF
        cm=mp.det(defect).real
        gap=mp.mpf(8)/25-contrast
        row={"m":m,"T_error":str(T-targetT),"mean_a_error":str(a-targeta),"m_squared_deficit":str(m*m*gap),"m_squared_invariant":str(m*m*cm),"m_squared_left_log_correction":str(m*m*(ll+mp.log(3)/2)),"m_squared_right_log_correction":str(m*m*lr)}
        rows.append(row)
        assert abs(T-targetT)<mp.mpf("1e-60") and abs(a-targeta)<mp.mpf("1e-60")
    return {"precision_digits":80,"targets":{"T":"12/25","a":"8/25","P":4,"Q":2,"kM":1},"rows":rows,"expected_limits":{"m_squared_deficit":"1/20","m_squared_invariant":"1/12","left_log_correction":"-25/576","right_log_correction":"13/576"},"claim":"Arbitrary-precision exact-layer model plus numerical root solve; not an implicit-function proof or formal theorem."}


def full_sphere_dipoles():
    k=1.0
    mu,weights=np.polynomial.legendre.leggauss(35)
    phi=np.linspace(0,2*np.pi,70,endpoint=False)
    ns=np.array([[np.sqrt(1-u*u)*np.cos(v),np.sqrt(1-u*u)*np.sin(v),u] for u in mu for v in phi])
    ws=np.repeat(weights,len(phi))*2*np.pi/len(phi)
    J=np.diag([1,1,1,1j,1j,1j]);D=np.diag([1,1,1,-1,-1,-1])
    records=[]
    for t in [-.999,-.4,0.,.7,.99999999]:
        b=np.sqrt((1-t*t)/2)
        A=np.zeros((6,6),dtype=complex)
        active=[0,4,1]
        A[np.ix_(active,active)]=.5j*np.array([[1-t,0,-b],[0,1-t,-b],[-b,b,1]])
        assert np.linalg.norm(A.T-D@A@D)<1e-14
        QA=(A-A.conj().T)/(2j)-A.conj().T@A
        minimum=float(np.linalg.eigvalsh(QA).min())
        aa=np.sqrt(2*(1-t)/(1+t))
        bare=1j*np.array([[aa*aa,-aa*aa/2,-aa],[aa*aa/2,0,-aa],[-aa,aa,1]])
        dressed=la.inv(la.inv(bare)-1j*np.eye(3))
        dressing_error=float(np.linalg.norm(dressed-A[np.ix_(active,active)]))
        for sign in [1,-1]:
            f=np.zeros(6,dtype=complex);f[0]=1;f[4]=sign
            af=A@f
            field=3/(2*k)*(af[:3]-ns*np.sum(ns*af[:3],axis=1)[:,None]-np.cross(ns,af[3:]))
            integrated=float(np.sum(ws*np.sum(abs(field)**2,axis=1)))
            expected=float(6*np.pi/(k*k)*np.vdot(af,af).real)
            ext=float(6*np.pi/(k*k)*np.vdot(f,af).imag)
            absorption=float(6*np.pi/(k*k)*np.vdot(f,QA@f).real)
            records.append({"t":t,"direction":sign,"sphere_scattering":integrated,"quadratic_scattering":expected,"difference":integrated-expected,"extinction":ext,"absorption":absorption,"minimum_QA_eigenvalue":minimum,"radiation_dressing_error":dressing_error})
            assert abs(integrated-expected)<1e-11
            assert minimum>-1e-12
    return {"polar_quadrature":35,"azimuthal_points":70,"samples":records,"claim":"Complete-sphere quadrature of actual electric-plus-magnetic far-field formula."}


def dense_dda(R,grid,t=.7,eta=.8,delta=.002,h=1.0,d=.5):
    k=2*np.pi;dx=1/grid
    nxy=round(R/dx);nzA=round(h/dx);nzW=round(d/dx)
    assert abs(nxy*dx-R)<1e-12 and abs(nzA*dx-h)<1e-12 and abs(nzW*dx-d)<1e-12
    xy=(np.arange(nxy)+.5)*dx-R/2
    z=(np.arange(nzA+nzW)+.5)*dx
    points=np.array([[x,y,zz] for x in xy for y in xy for zz in z])
    N=len(points)
    ss=np.sqrt(1-t*t);V=np.array([[-t,ss],[ss,t]])
    eA=np.diag([1+1j*(eta+delta),1+1j*delta,1+1j*delta])
    eW=np.zeros((3,3),dtype=complex)
    eW[:2,:2]=(5*np.eye(2)-3*V)/2+1j*delta*np.eye(2);eW[2,2]=1+1j*delta
    eps=np.array([eA if p[2]<h else eW for p in points])
    I=np.eye(3)
    al0inv=np.array([(ep+2*I)@np.linalg.inv(ep-I)/(3*dx**3) for ep in eps])
    radiation=k**3/(6*np.pi)
    alinv=al0inv-1j*radiation*I
    diff=points[:,None,:]-points[None,:,:]
    distances=np.linalg.norm(diff,axis=2)
    offdiag=distances>0
    rr=np.where(offdiag,distances,1)
    nn=diff/rr[:,:,None]
    outer=nn[:,:,:,None]*nn[:,:,None,:]
    kd=k*rr
    G4=np.exp(1j*kd)[:,:,None,None]/(4*np.pi*rr**3)[:,:,None,None]*(
        (kd**2+1j*kd-1)[:,:,None,None]*I+(-kd**2-3j*kd+3)[:,:,None,None]*outer)
    G4[~offdiag]=0
    G=G4.transpose(0,2,1,3).reshape(3*N,3*N)
    M=-G.copy()
    for ii in range(N):M[3*ii:3*ii+3,3*ii:3*ii+3]+=alinv[ii]
    rhs=np.zeros((3*N,2),dtype=complex)
    rhs[1::3,0]=np.exp(1j*k*points[:,2]);rhs[1::3,1]=np.exp(-1j*k*points[:,2])
    p=la.solve(M,rhs,assume_a="sym")
    loss=-(al0inv-al0inv.conj().transpose(0,2,1))/(2j)
    records=[]
    for sign in range(2):
        pi=p[:,sign].reshape(N,3)
        ext=k*np.vdot(rhs[:,sign],p[:,sign]).imag
        absorption=k*np.einsum("ni,nij,nj->",pi.conj(),loss,pi).real
        scatter=k*(radiation*np.vdot(p[:,sign],p[:,sign]).real+np.vdot(p[:,sign],G@p[:,sign]).imag)
        residual=float(np.linalg.norm(M@p[:,sign]-rhs[:,sign])/np.linalg.norm(rhs[:,sign]))
        records.append({"sigma_ext":float(ext),"sigma_abs":float(absorption),"sigma_sca":float(scatter),"relative_residual":residual,"optical_theorem_error":float(ext-absorption-scatter)})
    # Independent far-field angular integration for this finite model.
    mu,w=np.polynomial.legendre.leggauss(28);phi=np.linspace(0,2*np.pi,56,endpoint=False)
    ns=np.array([[np.sqrt(1-u*u)*np.cos(v),np.sqrt(1-u*u)*np.sin(v),u] for u in mu for v in phi])
    ws=np.repeat(w,len(phi))*2*np.pi/len(phi)
    phase=np.exp(-1j*k*(ns@points.T))
    sphere=[]
    for sign in range(2):
        transform=phase@p[:,sign].reshape(N,3)
        far=k*k/(4*np.pi)*(transform-ns*np.sum(ns*transform,axis=1)[:,None])
        val=float(np.sum(ws*np.sum(abs(far)**2,axis=1)))
        sphere.append({"quadrature_scattering":val,"minus_Gram_scattering":val-records[sign]["sigma_sca"]})
    gamma=abs(records[0]["sigma_abs"]-records[1]["sigma_abs"])/records[0]["sigma_ext"]
    return {"square_side_in_wavelengths":R,"cells_per_wavelength":grid,"cells":N,"observables":records,"Gamma":float(gamma),"opposite_extinction_difference":records[0]["sigma_ext"]-records[1]["sigma_ext"],"sphere_checks":sphere,"claim":"Solved dense nonperiodic retarded point-dipole system, not a continuum-converged Maxwell body."}


def main():
    lightweight="--lightweight" in sys.argv
    out={"python":sys.version,"numpy":np.__version__,"scipy":scipy.__version__,"sympy":sp.__version__,"mpmath":mp.__version__,"authorship":"Independently written for audit B; no paper's numerical program imported.","symbolic":symbolic_checks(),"random_symmetric_contractions":contraction_search(),"grazing":grazing_check(),"grazing_Green_operator_growth":grazing_operator_lower_bound(),"planar":planar_checks(),"thickness_benchmark":thickness_benchmark(),"dipole_radiation":full_sphere_dipoles()}
    (HERE/"audit_b_results.json").write_text(json.dumps(out,indent=2),encoding="utf-8")
    print("Symbolic, grazing, planar, thickness and dipole checks saved.",flush=True)
    if not lightweight:
        out["finite_dense_DDA"]=[]
        for R,grid in [(0.5,4),(0.5,6),(1.0,4),(1.0,6),(1.5,4),(1.5,6),(1.0,8)]:
            rec=dense_dda(R,grid)
            out["finite_dense_DDA"].append(rec)
            (HERE/"audit_b_results.json").write_text(json.dumps(out,indent=2),encoding="utf-8")
            print(f"Dense DDA R={R}, grid={grid}, cells={rec['cells']}, Gamma={rec['Gamma']:.12f}",flush=True)
    print("All requested checks completed.",flush=True)


if __name__=="__main__":
    main()
