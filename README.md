# bizcoq2021

**BMETE91AM58**

Molnár Zoltán Gábor, 

BME TTK Algebra Tsz., 

mozow@math.bme.hu

## Telepítés

Mindenféle szoftverek, manualok, modulok, stb. elérhetősége alapvetően itt:

> https://coq.inria.fr/

_Win_: [Get Coq](https://coq.inria.fr/download) fül alatt a Win verzió letöltő linkje, már az első bekezdésben megvan. Aki Emacs-ot használ vagy használna, annak további ismertető: [pdf](http://staff.ustc.edu.cn/~xyfeng/teaching/TOPL/reading/ProofGeneral.pdf). Ehhez szükséges a Proof General nevű szerkesztő, amit az Emacs meghív. Aki nem szereti az Emacs-ot, annak a rendelkezésére áll a **CoqIDE** szerkesztő program, ami a Coq telepítése után az egyetlen futtatható file abban a könyvtárban.

_Linux_: Ubuntu alatt az alap vagy Synaptic csomagkezelőben elérhető a Coq-ra rákeresve. Akinek nem Ubuntuja van, az meg úgy is olyan okos, hogy annak magától is menni fog. CoqIDE szintén megtalálható, amennyiben az Emacs nem szimpi.

## Érintett témák

<!--
1. óra leírása: [itt](eloadas/1_bevezetes/) és a [.v file](eloadas/1_bevezetes/bizcoq_1.v). (Tanult parancsok és taktikák: Definition, Show Proof, Check, Print, SerachAbout, "match ... with |", reflexivity, unfold ..., apply ..., exact, assumption.)

2. óra leírása: [itt](eloadas/2_bonyolultabb/) és a [.v file](eloadas/2_bonyolultabb/bizcoq_2.v). (Tanult parancsok és taktikák: Structure, "induction x, y; auto; right; discriminate.")

3. óra leírása: [itt](eloadas/3_fák_listák/) és a [.v file](eloadas/3_fák_listák/bizcoq_3.v). (Tanult parancsok és taktikák: Require Import Omega (meg minden), Fixpoint (azaz rekurzív definíció), induction x, simpl, congruence, rewrite IHx.) 
-->

Lásd  [előadás](eloadas) mappa.

1. bool és Prop adattípusok és érvelés velük
2. nat, tree, list és minden: az induktív adattípusok, primitív rekurzív függvények
3. monadizáció, side effectek kezelése
4. Curry--Howard-izomorfizmus, lambda kalkulus és funkcionális programozás
5. matematikai elméletek beprogramozása és bizonyítások
6. egyszerű, polimorf és függő típusok

## Követelmények
Aktív órai jelenlét, minden második alkalomra házik készítése, két beadandó feladatcsomag a 7. és 13. héten. 

## Egyebek

Hivatalos cuccok: https://math.bme.hu/~mozow/biz_coq.html.

LaTeX konverter md file-hoz: https://jsfiddle.net/8ndx694g/.

Github markup puska: https://github.com/adam-p/markdown-here/wiki/Markdown-Cheatsheet.

Természetes számok kezelése: Adam Chlipala spéci taktikái ([v](forrasok/CpdtTactics.v)) a nat típusban való számolások kezelésére (pl. "crush" taktika) (leírás: [net](http://adam.chlipala.net/cpdt/)). Hasonlóképpen kiválóan kezeli a matematikai témákat a [Mathematical Components](https://math-comp.github.io/). 

Leveztésfa készítő csomagok LaTeX-ben ([pdf](latex_sablon/levezetesfa.pdf), [tex](latex_sablon/levezetesfa.tex)).

Coq jelölés, taktika és definíció Cheat Sheet: [pdf](https://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf).
