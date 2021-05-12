# Kifejezőképesség próbája

Az automatikus bizonyításellenőrző programok egyik szokásos tesztje az úgy nevezett Drinker's Paradox. Ez a következő:

<img src="https://render.githubusercontent.com/render/math?math=%5Cvdash_%7BCL%7D(%5Cexists%20%5C!x)(((%5Cexists%20%5C!%20x)A(x))%5Cto%20A(x))">

Vagyis van olyan, aki ha bárki iszik, ő is iszik. A duálisa: 

<img src="https://render.githubusercontent.com/render/math?math=%5Cvdash_%7BCL%7D(%5Cexists%20%5C!%20x)(A(x)%5Cto(%5Cforall%5C!%20x)A(x))">

azaz, van olyan, aki ha iszik, mindenki iszik. Ezek a klasszikus logika paradoxonai, azaz nem ellentmondások, csak furcsák. Hogy mi bennük a furcsa, az majd a bizonyításukból, ill. a BHK-interpretációbeli cáfolatukból fog kiderülni.

**Informális levezetés a klasszikus logikában.** Két eset van. Vagy igaz (∃x)A(x) vagy hamis. Ha igaz, akkor vehetünk egy olyan _a_ dolgot, amire igaz A(_a_). Mivel igazból következik az igaz, így ((∃x)A(x)) → A(_a_) igaz, hogy (∃x)(((∃x)A(x)) → A(x)). Ha (∃x)A(x) hamis, akkor bármilyen _a_-ra ((∃x)A(x)) → A(_a_), mert hamisból minden következik.

**BHK-cáfolat** Ha lenne (∃x)(((∃x)A(x)) → A(x))-nak konstruktív levezetése, akkor lenne _a_, hogy ((∃x)A(x)) → A(_a_). Ez az _a_ viszont független kell, hogy legyen A-tól, mert nem feltételezhetjük, hogy (∃x)A(x)-nak van igazságértéke.  
