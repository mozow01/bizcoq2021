# GIT crash course

Aki még nem találkozott a Gittel annak elsőre ijesztő lesz. Megmutatnék pár alapfogást, hogy kényelmes és hatékony legyen a közös munka.

## Hogyan kezdjem el?

Telepíts fel valamiféle Git klienst. Windowsra úgy tudom a GitHub maga is ad ilyet, linuxon egyszerűen:

```bash
sudo apt install git
```

Most le kell töltened a tárolót. Ezt így teheted meg Terminálban, vagy parancssorban:
```
git clone https://github.com/mozow01/bizcoq2021.git
```

Ez létrehoz nálad egy `bizcoq2021` nevű mappát, ebbe tudsz majd dolgozni.

## Hogyan kövessem az órát?
Lépj be a mappába, és add ki a következő utasítást:
```
git pull
```
Ez le fogja tölteni a legfrissebb verziót a tárolóból, így megkapod a többiek munkáját.

## Hogyan küldhetek be saját tartalmat?
A munkamappában állítsd elő a szükséges fájlokat, készítsd el a programot. Ha megvan, meg kell mondanod a Gitnek, hogy ezt a fájlt is kövesse:
```
git add programom.v
```
Ha változtattál valamit, a legegyszerűbb ha globálisan hozzáadod:
```
git add -A
```
Ezután "el kell követned" a módosításokat:
```
git commit -m "Git útmutató v0.1 hozzáadása"
```
Ez a parancs befűzi a tárolóba a módosításaidat az adott üzenettel. Érdemes ezt jól kitölteni, hogy tudják a többiek mi van abban a commitban, és ha kell, vissza lehessen térni a megelőző állapotra.

Ha ez megvan, a szerverre fel kell töltened a módosításokat:
```
git push
```

## Baj van!
A szerver nem engedi hogy feltoljam a commitomat!

Ez a legtöbb esetben azért van, mert a szerveren a tároló "már előtted van", nincs meg nálad minden változás. Ilyenkor le kell töltened ami változott:
```
git pull
```
A Git nagyon okosan meg fogja találni a te változtatásaid különbségét a szerver verziójával, és alkalmazza amit csak lehet. Legtöbb esetben sikerül is, commitolhatsz azonnal.

Ha nem, akkor már gondolkodást igényel a probléma: ki fogja írni az ütköző változtatásokat, ezeket neked manuálisan ki kell javítani. Csak utána szabad `git add ...` művelettel hozzáadnod a kézzel javított fájlokat, majd commitolnod, pusholnod.
