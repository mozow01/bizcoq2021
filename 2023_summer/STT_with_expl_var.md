# Simple Type Theory with Explicit Variables

Ez egy típusos programozási nyelv változódeklarációval, melyben a változók névvel szerepelnek. A típusokat, a pogramokat és a változókörnyezeteket is rekurzívan definiáljuk.

**Típusok:**

<img align="center" src="https://i.upmath.me/svg/%5Cfrac%7B%7D%7B%5Ciota%20%3A%20%5Ctext%7BType%7D%7D%5Cqquad%5Cfrac%7BA%3A%5Ctext%7BType%7D%5Cquad%20B%3A%5Ctext%7BType%7D%7D%7BA%5Cto%20B%3A%20%5Ctext%7BType%7D%7D" alt="\frac{}{\iota : \text{Type}}\qquad\frac{A:\text{Type}\quad B:\text{Type}}{A\to B: \text{Type}}" />

Konstans típus (mint &iota;) bármennyi lehet és bármilyen, például: nat, bool. 

Összetett típusra példa (most csak függvénytípusaink vannak) <img align="center" src="https://i.upmath.me/svg/(A%5Cto%20%20B)%20%5Cto%20A%2C%5Cqquad%20A%5Cto%20(%20B%20%5Cto%20A%20)%5Cquad%20%5Cleft(%5Coverset%7B%5Ctext%7Bdef.%7D%7D%7B%3D%7DA%5Cto%20%20B%20%5Cto%20A%20%5Cright)%20%20%20" alt="(A\to  B) \to A,\qquad A\to ( B \to A )\quad \left(\overset{\text{def.}}{=}A\to  B \to A \right)   " />

&rarr; _jobbra asszociált,_ azaz: A&rarr;B&rarr;C = A&rarr;(B&rarr;C)

**Explicit változók:**

<img align="center" src="https://i.upmath.me/svg/x%2Cy%2Cz%2C..." alt="x,y,z,..." /> : Var

**Valtozódeklarációk** (kontextusok, környezetek):

<img align="center" src="https://i.upmath.me/svg/%5Cfrac%7B%7D%7B%20%5Cemptyset%20%3A%20%5Ctext%7BContext%7D%7D%2C%5Cqquad%20%5Cfrac%7B%5CGamma%20%3A%20%5Ctext%7BContext%7D%5Cqquad%20x%3A%5Ctext%7BVar%7D%5Cqquad%20A%3A%5Ctext%7BType%7D%7D%7B%5CGamma%5Ccup%5C%7B(x%2CA)%5C%7D%20%3A%20%5Ctext%7BContext%7D%7D" alt="\frac{}{ \emptyset : \text{Context}},\qquad \frac{\Gamma : \text{Context}\qquad x:\text{Var}\qquad A:\text{Type}}{\Gamma\cup\{(x,A)\} : \text{Context}}" />

Ha &Gamma; egyszerűen x:A -k listája, és nem valami explicit rekurzív relációval definiált kifejezés, akkor a rendszer _kontextuális típuselmélet:_

<img align="center" src="https://i.upmath.me/svg/%5Cfrac%7B%7D%7B%20%5Ctext%7Bnill%7D%20%3A%20%5Ctext%7BContext%7D%7D%2C%5Cqquad%20%5Cfrac%7B%5CGamma%20%3A%20%5Ctext%7BContext%7D%5Cqquad%20x%3A%5Ctext%7BVar%7D%5Cqquad%20A%3A%5Ctext%7BType%7D%7D%7B((x%3AA)%20%3A%3A%5CGamma)%20%3A%20%5Ctext%7BContext%7D%7D" alt="\frac{}{ \text{nill} : \text{Context}},\qquad \frac{\Gamma : \text{Context}\qquad x:\text{Var}\qquad A:\text{Type}}{((x:A) ::\Gamma) : \text{Context}}" />

ahol nill az üres lista, :: a lista bővítése balról.

Pl.: 

{y : &iota;} csak egy atomi típusú változó (mondjuk: n : nat)

{x : A&rarr;B, z : A} két változó is van, egy konstans és egy függvény (pl.: f : nat&rarr;nat, n : nat).

**Típusos kifejezések:**

<img align="center" src="https://i.upmath.me/svg/%5Cfrac%7B%7D%7B%5CGamma%5Ccup%5C%7B(x%2CA)%5C%7D%20%5Cvdash%20x%3AA%20%7D" alt="\frac{}{\Gamma\cup\{(x,A)\} \vdash x:A }" />

<img align="center" src="https://i.upmath.me/svg/%5Cfrac%7B%5CGamma%20%5Cvdash%20P%3AA%5Cto%20B%5Cqquad%20%5CGamma%20%5Cvdash%20Q%3AA%7D%7B%5CGamma%20%5Cvdash%20P%20Q%3AB%7D%2C%5Cqquad%20%5Cfrac%7B%5CGamma%5Ccup%5C%7B(x%2CA)%5C%7D%20%5Cvdash%20P%3AB%7D%7B%5CGamma%20%5Cvdash%20%5Clambda%20x%5Ccolon%20%5C!%5C!A.%20P%3AA%5Cto%20B%7D" alt="\frac{\Gamma \vdash P:A\to B\qquad \Gamma \vdash Q:A}{\Gamma \vdash P Q:B},\qquad \frac{\Gamma\cup\{(x,A)\} \vdash P:B}{\Gamma \vdash \lambda x\colon \!\!A. P:A\to B}" />

(van egy csomó implicit premissza, persze)

&vdash; jelentése: _levezethetőség_ vagy _típusolhatóság_ vagy a legismertebb: _típusinferálás_ pl. a Matlabban vagy a Typescript-ben.

A levezetési szabályok jelentése: 

PQ kódolja a függvénykiszámítás feladatát egy adott helyen (nem végzi el, ez csak egy utasítás). Néha PQ-t P&dollar;Q-ral jelölik. PQ _balra asszociált:_ PQR = (PQ)R  (P&dollar;Q&dollar;R = (P&dollar;Q)&dollar;R).

&lambda;x.P kódolja azt a függvényt, ami az x imputból a P-t számítja ki. &lambda; hatóköre a lehető legtágabb jobbra: &lambda;x.PQ = &lambda;x.(PQ).

**Programfuttatás:**

<img align="center" src="https://i.upmath.me/svg/%5Cfrac%7B%5CGamma%5Cvdash%20P%3AA%5Cto%20B%5Cqquad%20%5CGamma%5Cvdash%20Q%3AA%7D%7B%5CGamma%5Cvdash%20(%5Clambda%20x%5Ccolon%5C!%5C!A.P)Q%5Cequiv%20P%5Bx%2F%20Q%5D%3AB%7D%5Cquad%20(%5Cbeta%5Ctext%7B-redukci%C3%B3%7D)" alt="\frac{\Gamma\vdash P:A\to B\qquad \Gamma\vdash Q:A}{\Gamma\vdash (\lambda x\colon\!\!A.P)Q\equiv P[x/ Q]:B}\quad (\beta\text{-redukció})" />

Itt 

<img align="center" src="https://i.upmath.me/svg/P%5Bx%2F%20Q%5D" alt="P[x/ Q]" /> 

az implicit helyettesítés.

**Példák:** 

**1.** Legyártunk az x:A&rarr;B és y:B&rarr;C programokból egy A&rarr;C típusú P programot. Sok ilyet lehet csinálni, de mi egy _kanonikusat_ fogunk csinálni.

<img align="center" src="https://i.upmath.me/svg/%5C%7Bx%3AA%5Cto%20B%2Cy%3AB%5Cto%20C%5C%7D%5Cvdash%20P%3AA%20%5Cto%20C" alt="\{x:A\to B,y:B\to C\}\vdash P:A \to C" />

A levezetés ez: 

<img src="https://i.upmath.me/svg/%5C%7Bz%3AA%2C%20x%3AA%5Cto%20B%2Cy%3AB%5Cto%20C%5C%7D%5Cvdash%20z%3AA" alt="\{z:A, x:A\to B,y:B\to C\}\vdash z:A" />

<img src="https://i.upmath.me/svg/%5C%7Bz%3AA%2C%20x%3AA%5Cto%20B%2Cy%3AB%5Cto%20C%5C%7D%5Cvdash%20xz%3AB" alt="\{z:A, x:A\to B,y:B\to C\}\vdash xz:B" />

<img src="https://i.upmath.me/svg/%5C%7Bz%3AA%2C%20x%3AA%5Cto%20B%2Cy%3AB%5Cto%20C%5C%7D%5Cvdash%20y(xz)%3AC" alt="\{z:A, x:A\to B,y:B\to C\}\vdash y(xz):C" />

<img src="https://i.upmath.me/svg/%5C%7Bx%3AA%5Cto%20B%2Cy%3AB%5Cto%20C%5C%7D%5Cvdash%20%5Clambda%20x%5Ccolon%20%5C!%5C!A.y(xz)%3AA%5Cto%20C" alt="\{x:A\to B,y:B\to C\}\vdash \lambda x\colon \!\!A.y(xz):A\to C" />

**2.** Legyártunk egy A&rarr;B&rarr;A típusú programot csak a semmiből.

<img src="https://i.upmath.me/svg/%5Cvdash%20P%3AA%5Cto%20(B%5Cto%20A)" alt="\vdash P:A\to (B\to A)" />

A levezetés ez: 

<img src="https://i.upmath.me/svg/%5C%7Bx%3AA%2Cy%3AB%5C%7D%5Cvdash%20x%3AA" alt="\{x:A,y:B\}\vdash x:A" />

<img src="https://i.upmath.me/svg/%5C%7Bx%3AA%5C%7D%5Cvdash%20%5Clambda%20y%5Ccolon%20%5C!%5C!B.x%3AB%5Cto%20A" alt="\{x:A\}\vdash \lambda y\colon \!\!B.x:B\to A" />

<img src="https://i.upmath.me/svg/%5Cvdash%20%5Clambda%20x%5Ccolon%20%5C!%5C!A.%5Clambda%20y%5Ccolon%20%5C!%5C!B.x%3AA%5Cto%20(B%5Cto%20A)" alt="\vdash \lambda x\colon \!\!A.\lambda y\colon \!\!B.x:A\to (B\to A)" />
















