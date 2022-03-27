#  A filozófia csodálatos hatékonysága az automatikus tételbizonyításban
Molnár Zoltán Gábor, Algebra Tsz.

## Coq automatikus bizonyító és bizonyításmenedzselő program

Thierry Coquand, Christine Paulin-Mohring implementálták számítógépesen az _Induktív Konstrukciók Kalkulusát_ (CIC, CoC, Coq), ami Peer Martin-Löf típuselméletének átdolgozása. 

## Mi az az induktív adattípus?

Alappélda: a **természetes számok** halmaza, mint rekurzívan definiált sorozat (nat).

Konstruktorok:

<img src="https://render.githubusercontent.com/render/math?math=0%3A%5Ctext%7Bnat%7D">

<img src="https://render.githubusercontent.com/render/math?math=S%3A%5Ctext%7Bnat%7D%5Cto%20%5Ctext%7Bnat%7D">

Indukciós szabály:

<img src="https://render.githubusercontent.com/render/math?math=%5Cdfrac%7BP(0)%2C%5Cquad%20%5Cforall%20n%3A%5Ctext%7Bnat%7D%2C%20P(n)%5Cto%20P(Sn)%7D%7B%5Cforall%20n%3A%5Ctext%7Bnat%7D%2C%20P(n)%7D">



"Szemléletesen, egy induktívan definiált típus konstruktorok egy teljes listája által adott. A nekik megfelelő indukciós elvvel érvelünk a típus elemeivel kapcsolatban és a konstruktorokon függvényeket adunk meg, amik alkamasak az egész típus felett értelmezett primitív rekurzív függvények definiálására." 
