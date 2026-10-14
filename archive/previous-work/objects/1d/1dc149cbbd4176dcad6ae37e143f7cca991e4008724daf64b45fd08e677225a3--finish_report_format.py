from pathlib import Path
p=Path(r"C:\Users\Daniel\.codex\.chatgpt-projects\g-p-6ac8784424248191b154eb2ed308e1f1\outputs\OQ7-priority-20261013-7d4b21a9\TARGETED_PRIORITY_REPORT.md")
s=p.read_text(encoding="utf-8")
for expr in ["X=0","A_+","1/2","P>1,Q>0","E_*>0","k","R","x","y","1-|T|^2"]:
    s=s.replace("("+expr+")","$"+expr+"$")
s=s.replace("This gives a necessary efficiency/directivity constraint, not the required two-source dielectric construction.","This gives a necessary efficiency/directivity constraint, not the required two-source dielectric construction. [Primary Eq. (22)](https://vbn.aau.dk/ws/files/19704710/Absorption_Efficiency.pdf).")
s=s.replace("The local-material and exact-target requirements remain additional obligations.","The local-material and exact-target requirements remain additional obligations. [Primary Eqs. (2)–(3)](https://link.aps.org/accepted/10.1103/PhysRevLett.118.154302).")
p.write_text(s,encoding="utf-8",newline="\n")

