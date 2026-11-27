# Математикам и верификаторам Lean 4

Этот раздел посвящён чистой конструктивной математике **Книги V ([Математика проективного многообразия, PDF](https://github.com/AI-Guiders/discrete-quantum-mechanics/raw/main/book/out/pdf/projective-manifold-mathematics.pdf))** и архитектуре формальной верификации **`68/68` таргетов Lean 4** в репозитории [`AI-Guiders/dqm-lean`](https://github.com/AI-Guiders/dqm-lean) (сабмодуль `lean/`).

---

## 1. Безлазеечный компиляторный линтер ядра (`AxiomGuard.lean`)

В машинной верификации математики самая частая скрытая ошибка — **протаскивание недоказанных шагов в заголовок теоремы в виде именованных посылок `(h : P)`** либо опора на неконструктивные аксиомы (`Classical.choice`, `sorryAx`).

Каждый модуль в обоих контурах `lean/Constructive/` и `lean/MtCarrier/` автоматически проверяется на этапе компиляции линтером [`lean/Constructive/AxiomGuard.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/AxiomGuard.lean) через `initialize addLinter`:

1. **Ноль неконструктивных аксиом:** Каждая `theorem` проверяется в окружении ядра Lean 4 (`collectAxioms`). Любая зависимость от `Classical.choice`, `Classical.em`, `sorryAx` или пользовательских `axiom` вызывает ошибку компиляции. Разрешены только базовые аксиомы ядра `[propext, Quot.sound]` (и вычислительные редукции `native_decide`).
2. **Ноль протащенных `Prop`-гипотез в заголовке:** Линтер рекурсивно обходит Pi-телескоп (`forallE`) типа теоремы. Любая именованная гипотеза `(h : P)` типа `Prop` в шапке теоремы — кроме явных числовых границ области определения (`<`, `≤`, `>`, `≥`) — блокируется компилятором. **Никаких обходных префиксов имён (вроде `cond_`) не существует.**
3. **Защита от тавтологий:** Тривиальные заключения (`True`, синтаксическая рефлексивность `a = a`) отвергаются.

---

## 2. Конструктивная теория чисел и проективное исчисление (`lean/Constructive/`)

Книга V ([`projective-manifold-mathematics.pdf`](https://github.com/AI-Guiders/discrete-quantum-mechanics/raw/main/book/out/pdf/projective-manifold-mathematics.pdf)) содержит только безусловно доказанные конструктивные теоремы из `lean/Constructive/`:

| Модуль | Доказанный математический результат |
| :--- | :--- |
| [`BipyramidGeometry.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/BipyramidGeometry.lean) | Целочисленный 512-тактовый бипирамидальный фазовый круг, точное пифагорово тождество $(C(\varphi))^2 + (S(\varphi))^2$, $L_1$-инвариант грани и первый возврат параболы с периодом 1024 |
| [`RotatorQuadrature.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/RotatorQuadrature.lean) | Точные бескорневые дискретные квадратуры: интегралы Френеля, эллиптический интеграл Якоби $\mathcal{K}_{\mathrm{ell}}(1,1)=65\,536$, ядро Дирихле, функция Бесселя $J_0$ и 12-лучевая кубатура сферы Архимеда |
| [`PillaiDiophantine.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/PillaiDiophantine.lean) | Обобщённый диофантов движок Пиллаи ($a^x - b^y = c$), единственность решения Каталана $3^2 - 2^3 = 1$ и оценки фазовой сепарации |
| [`AbcPlanetaryWronskian.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/AbcPlanetaryWronskian.lean) | Конструктивные тождества для определителя Вронского и явные оценки голономии $abc$-троек и отношения Спиро |
| [`CollatzPlanetarySplice.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/CollatzPlanetarySplice.lean) | Точные тождества 2-адического стока ($3^k \cdot n + \dots$) и детерминированный 12-лучевой автомат склейки ветвей |
| [`RiemannHolonomy.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/RiemannHolonomy.lean) | Ортогональность контрволнового каскада на $\varphi \in [0, 512]$, строгая **трихотомия** ($\varphi = 128$, $\varphi = 384$ или $C(\varphi) \neq 0$) и **доказательство независимости (Модель 1 vs Модель 2)**, показывающее, что симметричный захват нулей ($\varphi = 128$) против смещённой фазы ($\varphi = 129$) независим от базовой аксиоматики без аксиомы самодвойственности |

---

## 3. Двенадцать дисциплинарных модулей носителя (`lean/MtCarrier/`)

Все прикладные и естественнонаучные операторы разложены в 12 чистых модулей внутри `lean/MtCarrier/` (собираемых через `UnifiedOperators.lean` и проверяемых в `AxiomAudit.lean`):

1. **`ContinuumPhysics.lean`** — Изотропный лапласиан $\Delta_{O_2}$, тензор деформаций, квантовый дефицит Бома, алгебра Паули — Клиффорда, $\alpha_{\mathrm{fs}}^{-1} \in \mathbb{Q}(\sqrt{2})$ и $587\times$ сжатие барьера.
2. **`CosmologyHalo.lean`** — Вакуумное гало голономии $16/3$ и плоские кривые вращения галактик без тёмной материи.
3. **`ChemicalBonding.lean`** — Ковалентная связь, закон Гесса, правила Вудворда — Хоффмана, катализ и граница Белла — Цирельсона $S_{\mathrm{QM}}^2 = (16/9)\,S_{\mathrm{LHV}}^2$.
4. **`OntogenyMutagenesis.lean`** — Гомоморфизм марковского одеяла среды в геном, мутагенез `CpG` и обратный компилятор фенотипа в ДНК.
5. **`PlanetogenesisAllometry.lean`** — 6 зон протопланетного диска, отбор биометаллов, аллометрия Клейбера 3/4 и 3 атмосферных фотонных окна.
6. **`NuclearShells.lean`** — Масштабная инвариантность $K^2$, 8 периодов таблицы Менделеева, остров стабильности $N=184$, ядерная паста и несингулярное ядро чёрной дыры Паули ($833:1$).
7. **`ParticleSpectrum.lean`** — 13-узловой ротор электрона, 6 ароматов кварков, калибровочные бозоны, адронные мультиплеты и полное квантование фазового пространства.
8. **`SuperconductorBioCad.lean`** — Куперовское спаривание $2e$, критические температуры сверхпроводников (`TiNi`, `MgB₂`, купраты) и терапевтический био-САПР.
9. **`ReversibleComputing.lean`** — Баллистический шаг без тепла Ландауэра, правило Борна, редукция 3-SAT, синдромная телепортация и 81-ричный модем Гейзенберга.
10. **`RotatorQuadratureCarrier.lean`** — Квадратуры на носителе и теорема внутреннего наблюдателя.
11. **`HardwarePhotovoltaics.lean`** — Барьер демона Лапласа, бабочка Грея, 4-канальный томограф фон Неймана и бесфононный кремниевый фотокаскад.
12. **`MechanicsElasticity.lean`** — 4 режима упругости пружины, предел циклической усталости металла $\sigma_{-1} \leftrightarrow 41$, скачок Бюргерса на потолке Паули $256$ и нелинейный упругий маятник.

---

## 4. Воспроизведение полной сборки `68/68` в Lean 4

```bash
cd lean
lake build
```

Ожидаемый финальный вывод:
```text
✔ [66/68] Built MtCarrier
Build completed successfully (68 jobs).
```
