# Simple Type Theory with Explicite Varables

Ez egy típusos programozási nyelv változódeklarációval, melyben a változók névvel szerepelnek. A típusokat, a pogramokat és a változókörnyezeteket is rekurzívan definiáljuk.

Típusok:

<img align="center" src="https://i.upmath.me/svg/%5Cfrac%7B%7D%7B%5Ciota%20%3A%20%5Ctext%7BType%7D%7D%5Cqquad%5Cfrac%7BA%3A%5Ctext%7BType%7D%5Cquad%20B%3A%5Ctext%7BType%7D%7D%7BA%5Cto%20B%3A%20%5Ctext%7BType%7D%7D" alt="\frac{}{\iota : \text{Type}}\qquad\frac{A:\text{Type}\quad B:\text{Type}}{A\to B: \text{Type}}" />

Pl.:  <img align="center" src="https://i.upmath.me/svg/(A%5Cto%20%20B)%20%5Cto%20A%2C%5Cqquad%20A%5Cto%20(%20B%20%5Cto%20A%20)%5Cquad%20%5Cleft(%5Coverset%7B%5Ctext%7Bdef.%7D%7D%7B%3D%7DA%5Cto%20%20B%20%5Cto%20A%20%5Cright)%20%20%20" alt="(A\to  B) \to A,\qquad A\to ( B \to A )\quad \left(\overset{\text{def.}}{=}A\to  B \to A \right)   " />

Változók (Var)

<img align="center" src="https://i.upmath.me/svg/x%2Cy%2Cz%2C..." alt="x,y,z,..." />

Valtozódeklarációk (kontextusok, környezetek)

<img align="center" src="https://i.upmath.me/svg/%5Cfrac%7B%7D%7B%20%5Cdiamond%5Cvdash%7D%2C%5Cqquad%20%5Cfrac%7B%5CGamma%5Cvdash%5Cqquad%20x%3A%5Ctext%7BVar%20%5Cqquad%20A%3A%5Ctext%7BType%7D%7D%7D%7B%5CGamma%2Cx%3AA%20%5Cvdash%7D" alt="\frac{}{ \diamond\vdash},\qquad \frac{\Gamma\vdash\qquad x:\text{Var \qquad A:\text{Type}}}{\Gamma,x:A \vdash}" />

Ha &Gamma; egyszerűen egy x:A-k listája, akkor a rendszer kontextuális típuselmélet.









