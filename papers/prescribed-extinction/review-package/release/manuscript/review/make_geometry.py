"""One vector drawing specification produces the PDF and SVG versions of Figure 1."""
from pathlib import Path
from math import sin, cos, atan2, pi
from html import escape
from reportlab.pdfgen import canvas
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.colors import HexColor

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "figures"
OUT.mkdir(exist_ok=True)
W, H = 800, 310
pdfmetrics.registerFont(TTFont("OQ7Figure", r"C:\Windows\Fonts\segoeui.ttf"))
svg = ['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 800 310" role="img" aria-labelledby="title desc">',
       '<title id="title">Finite two-layer dielectric and transverse axes</title>',
       '<desc id="desc">The absorber lies between z=0 and z=h; the plate between z=h and z=h+d. Both have square aperture R by R. Plus incidence propagates upward from the absorber side; minus incidence downward from the plate side. Both electric polarizations are e_y. The plate active axis u_theta is rotated from e_x toward e_y. Not to scale.</desc>',
       '<rect width="800" height="310" fill="white"/>']
c = canvas.Canvas(str(OUT / "two-layer-geometry.pdf"), pagesize=(W,H))
c.setTitle("Finite two-layer dielectric and transverse axes")
c.setAuthor("")
c.setFillColor(HexColor("#ffffff")); c.rect(0,0,W,H,fill=1,stroke=0)

def line(x1,y1,x2,y2,color="#25384a",width=1.4,dash=False):
    svg.append(f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{color}" stroke-width="{width}"'+(' stroke-dasharray="4 3"' if dash else '')+'/>')
    c.setStrokeColor(HexColor(color)); c.setLineWidth(width)
    c.setDash(4,3) if dash else c.setDash()
    c.line(x1,H-y1,x2,H-y2)

def poly(points,color="#25384a",fill=False,width=1.4):
    coords=" ".join(f"{x:.3f},{y:.3f}" for x,y in points)
    svg.append(f'<{"polygon" if fill else "polyline"} points="{coords}" stroke="{color}" stroke-width="{width}" fill="{color if fill else "none"}"/>')
    c.setStrokeColor(HexColor(color)); c.setFillColor(HexColor(color)); c.setLineWidth(width); c.setDash()
    p=c.beginPath(); p.moveTo(points[0][0],H-points[0][1])
    for x,y in points[1:]: p.lineTo(x,H-y)
    if fill: p.close()
    c.drawPath(p,stroke=1,fill=int(fill))

def arrow(x1,y1,x2,y2,color="#25384a",width=1.6):
    line(x1,y1,x2,y2,color,width)
    a=atan2(y2-y1,x2-x1); length=8
    poly([(x2,y2),(x2-length*cos(a-.4),y2-length*sin(a-.4)),(x2-length*cos(a+.4),y2-length*sin(a+.4))],color,True)

def text(x,y,s,size=14,color="#25384a",anchor="middle"):
    svg.append(f'<text x="{x}" y="{y}" fill="{color}" font-family="Segoe UI,Arial,sans-serif" font-size="{size}" text-anchor="{anchor}">{escape(s)}</text>')
    c.setFont("OQ7Figure",size); c.setFillColor(HexColor(color))
    fn={"middle":c.drawCentredString,"start":c.drawString,"end":c.drawRightString}[anchor]
    fn(x,H-y,s)

def rect(x,y,w,h,fill):
    svg.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" fill="{fill}" stroke="#25384a" stroke-width="1.4"/>')
    c.setFillColor(HexColor(fill)); c.setStrokeColor(HexColor("#25384a")); c.setLineWidth(1.4); c.setDash()
    c.rect(x,H-y-h,w,h,fill=1,stroke=1)

text(255,18,"Finite body: (x,z) section",16)
rect(140,78,230,62,"#dcebe9")
rect(140,140,230,66,"#f3e6d1")
text(255,105,"Plate",16); text(255,123,"active axis u_θ",13)
text(255,168,"Absorber",16); text(255,187,"active axis e_x",13)
for y,label in [(78,"z = h+d"),(140,"z = h"),(206,"z = 0")]:
    line(370,y,398,y,dash=True); text(405,y+4,label,13,anchor="start")
text(153,54,"vacuum",12,anchor="start"); text(153,246,"vacuum",12,anchor="start")
arrow(82,209,82,54); text(82,43,"e_z",14)
line(114,78,114,140); line(109,78,119,78); line(109,140,119,140); text(102,114,"d",14)
line(114,140,114,206); line(109,206,119,206); text(102,178,"h",14)
arrow(290,28,290,69,"#315c88"); text(307,37,"− incidence",13,anchor="start")
arrow(290,259,290,215,"#315c88"); text(307,252,"+ incidence",13,anchor="start")
line(140,277,370,277); line(140,272,140,282); line(370,272,370,282); text(255,274,"R",14)
text(255,301,"Square aperture R × R in (x,y)",13)

text(628,35,"Transverse axes",16)
arrow(570,199,720,199,"#93632b"); text(740,204,"e_x",14)
arrow(570,199,570,89,"#315c88"); text(570,76,"e_y",14)
angle=pi/6
arrow(570,199,570+135*cos(angle),199-135*sin(angle),"#28736c",2)
text(697,127,"u_θ",15,color="#28736c")
poly([(570+44*cos(t),199-44*sin(t)) for t in [angle*i/15 for i in range(16)]],width=1)
text(629,190,"θ",14)
text(633,252,"Incident polarization: e_y",14)
text(633,282,"Not to scale",12)
c.showPage(); c.save()
svg.append("</svg>")
(OUT/"two-layer-geometry.svg").write_text("\n".join(svg),encoding="utf-8")
print("Generated identical-specification vector PDF and SVG for Figure 1.")
