# Математикам и верификаторам Lean 4

Этот раздел посвящён чистой конструктивной математике **Книги V ([Математика проективного многообразия, PDF](https://github.com/AI-Guiders/discrete-quantum-mechanics/raw/main/book/out/pdf/projective-manifold-mathematics.pdf) · [Интерактивный граф теорем Lean 4 Blueprint](blueprint-book5/index.html))** и архитектуре формальной верификации **`81/81` таргетов Lean 4** в репозитории [`AI-Guiders/dqm-lean`](https://github.com/AI-Guiders/dqm-lean) (сабмодуль `lean/`).

---

## 1. Безлазеечный компиляторный линтер ядра (`AxiomGuard.lean`)

В машинной верификации математики самая частая скрытая ошибка — **протаскивание недоказанных шагов в заголовок теоремы в виде именованных посылок `(h : P)`** либо опора на неконструктивные аксиомы (`Classical.choice`, `sorryAx`).

Каждый модуль в обоих контурах `lean/Constructive/` и `lean/MtCarrier/` автоматически проверяется на этапе компиляции линтером [`lean/Constructive/AxiomGuard.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/AxiomGuard.lean) через `initialize addLinter`:

1. **Ноль неконструктивных аксиом:** Каждая `theorem` проверяется в окружении ядра Lean 4 (`collectAxioms`). Любая зависимость от `Classical.choice`, `Classical.em`, `sorryAx` или пользовательских `axiom` вызывает ошибку компиляции. Во всём математическом контуре `lean/Constructive/` (все 13 модулей) также **ноль (`0`) вызовов `native_decide`** — все теоремы Книги V доказаны чисто символьно в ядре Lean 4 (`[propext, Quot.sound]`).
2. **Ноль протащенных `Prop`-гипотез в заголовке:** Линтер рекурсивно обходит Pi-телескоп (`forallE`) типа теоремы. Любая именованная гипотеза `(h : P)` типа `Prop` в шапке теоремы — кроме явных числовых границ области определения (`<`, `≤`, `>`, `≥`) — блокируется компилятором. **Никаких обходных префиксов имён (вроде `cond_`) не существует.**
3. **Защита от тавтологий:** Тривиальные заключения (`True`, синтаксическая рефлексивность `a = a`) отвергаются.

---

## 2. Тринадцать модулей чистой конструктивной математики (`lean/Constructive/`)

Книга V ([`projective-manifold-mathematics.pdf`](https://github.com/AI-Guiders/discrete-quantum-mechanics/raw/main/book/out/pdf/projective-manifold-mathematics.pdf)) содержит только безусловно доказанные конструктивные теоремы из `lean/Constructive/` (`0 sorryAx`, `0 Classical.choice`, `0 native_decide`):

| Модуль | Доказанный математический результат |
| :--- | :--- |
| [`AxiomGuard.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/AxiomGuard.lean) | Компиляторный линтер ядра Lean 4 (`initialize addLinter constructiveKernelLinter`), блокирующий `sorryAx`, `Classical.choice`, протащенные `Prop`-посылки и тавтологии |
| [`RotatorQuadrature.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/RotatorQuadrature.lean) | Характер Эйлера на $\mathbb{Z}_{4Q}$, тождественно постоянный разностный вронскиан $\mathcal{W}_Q(\varphi)\equiv Q$, подъём Брахмагупты — Вейерштрасса на $S^1(\mathbb{Q})$, отсутствие делителей нуля, квадратуры Френеля, Якоби ($\mathcal{K}_{\mathrm{ell}}(1,1)=65\,536$), Дирихле, Парсеваля, Бесселя $J_0$, 12-лучевая кубатура Симпсона на $O_2(d)$ и поля $\mathbb{Q}(i)$, $\mathbb{Q}(\sqrt{2})$ |
| [`ProjectiveFieldCalculus.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/ProjectiveFieldCalculus.lean) | Разностный оператор производной над полем, вронскиан частного, вариационный принцип Эйлера — Лагранжа, бесполюсная башня производных частного $D^n(f/g)=N_n/G_n$ всех порядков $n\in\mathbb{N}$, круговое поле $\mathbb{Q}(i,\sqrt{2})=\mathbb{Q}(\zeta_8)$ и общий символьный закон стационарной фазы Френеля — Гаусса — Планшереля для произвольного масштаба $b\in\mathbb{Z}$ |
| [`InverseTrigHyperbolic.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/InverseTrigHyperbolic.lean) | Общая символьная биекция полярных и декартовых координат $(M,\varphi)\leftrightarrow(X,Y)=(M\mathcal{C}_Q(\varphi),M\mathcal{S}_Q(\varphi))$ для всех $Q,M,\varphi$ без квадратных корней и без рядов, точные $\operatorname{atan}_{L^1}$ и $\operatorname{acot}_{L^1}$, гиперболическая тройка Гудермана — Минковского $(\mathcal{Ch}_Q,\mathcal{Sh}_Q,D_{\mathrm{hyp}})$ и бескорневое/безлогарифмическое обращение гиперболических функций (`invHypQ`, `atanhCayley`, `acothCayley`) |
| [`LogicCohomology.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/LogicCohomology.lean) | Функционально полный булев базис Поста (`NOT, XOR, OR, AND`), редукция 3-SAT, конструктивные когомологии де Рама — Стокса — Гаусса ($d_1\circ d_0\equiv 0$, $d_2\circ d_1\equiv 0$) и конечное обращение нильпотентных операторов $(I+N_{\mathrm{nil}})^{-1}=I-N_{\mathrm{nil}}+N_{\mathrm{nil}}^2$ |
| [`PillaiDiophantine.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/PillaiDiophantine.lean) | Матричное представление двухуровневых ступеней $M_{a,b}\in\mathrm{Mat}_{2\times 2}(\mathbb{Z})$, изотропный конус в $\mathrm{SL}_2(\mathbb{Z})$, параболические жордановы матрицы, моноид башни аппроксимантов Паде, бескорневое кубическое сжатие с сокращением $X^3$ и закон ухода на соседний этаж |
| [`AbcPlanetaryWronskian.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/AbcPlanetaryWronskian.lean) | Трёхшахтные планетарные дифференциалы $\mathcal{A}+\mathcal{B}=\mathcal{C}$, факторизация определителя Ганкеля, кубический вронскиан Мейсона — Стотерса и проекторы Лагранжа — Вандермонда по дефектам нижних этажей |
| [`ModelTheoreticLimit.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/ModelTheoreticLimit.lean) | Алгебраические системы Мальцева, стабилизация проективной башни $\varprojlim M_n$, инвариантность интервального вронскиана медианты Штерна — Броко и матриц $\mathrm{SL}_2(\mathbb{Z})$, биективный стереографический изоморфизм $L^1(\mathbb{Z}_{4Q})\leftrightarrow S^1(\mathbb{C})$ и диагональная теорема Ловера — Тарского — Гёделя |
| [`CollatzPlanetarySplice.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/CollatzPlanetarySplice.lean) | Планетарный дифференциал Уиллиса $\mathrm{SL}_2(\mathbb{Z})\ltimes\mathbb{Z}^2$, башня двойного дрейфа, спуск Ферма, встречное прямое-обратное сшивание Безу и макрошаг сжигания единиц |
| [`CollatzGearMonoid.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/CollatzGearMonoid.lean) | Моноид бинарных слов шестерён, универсальная экстремальная огибающая остатка $3^B-2^B\le R_w\le 2^{A-B}(3^B-2^B)$, положительность вариационной производной транспозиции $\delta_{\mathrm{swap}}R_w = P_{L_1}Q_{L_2}\ge 1$ и отражение граничных неподвижных точек |
| [`RiemannHolonomy.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/RiemannHolonomy.lean) | Дисбаланс нормы Кэли, экватор Вейерштрасса ($\mathrm{Re}(s)=1/2\iff|w(s)|=1$), деструктивная интерференция встречных волн, простые каналы Эйлера, тождество радиального роста частотного вронскиана Коши — Римана, положительность Йенсена — Турана и минимум масштабной энергии Парсеваля |
| [`MinkowskiCounterwaveCascade.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/MinkowskiCounterwaveCascade.lean) | Парный вронскиан нулей Адамара, положительность бимодального ядра Якоби, многоэтажный каскад светового конуса Минковского — $\mathrm{SL}_2(\mathbb{Z})$, сокращение чётной матрицы Грама $\mathrm{MainAmount}_{\mathrm{vec}}$ при векторной суперпозиции мод и две конструктивные модели модельно-теоретической независимости |
| [`RotatorCalculusPaper.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/RotatorCalculusPaper.lean) | Объединяющий мост трёхшахтного планетарного дифференциала (`thm30`) и единые вариационные принципы экстремума (`thm36`) |

---

## 3. Восемнадцать дисциплинарных модулей физического носителя (`lean/MtCarrier/`)

Все естественнонаучные и инженерные операторы Книг I–IV разложены в 18 модулей внутри `lean/MtCarrier/` (собираемых через [`UnifiedOperators.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/UnifiedOperators.lean) под тем же компиляторным линтером `AxiomGuard.lean`):

1. **[`Spec.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/Spec.lean)** — Единственность решения уравнения Каталана $3^2 - 2^3 = 1$ ($d = 3$), геометрия кубооктаэдра $O_2(3)$ и кольца $\mathbb{Z}_{512}$.
2. **[`FaceAlgebra.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/FaceAlgebra.lean)** — Кусочно-линейный ротатор на $L^1$-алмазе, пифагоров подъём Вейерштрасса и 3 режима деления с остатком.
3. **[`HolonomyMaxwell.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/HolonomyMaxwell.lean)** — Дискретные уравнения Максвелла, тождества Стокса — Гаусса и закон индукции Фарадея.
4. **[`PolarVerletParabola.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/PolarVerletParabola.lean)** — Единственность полярного шага Верле из симплектического определителя $\det = 1$, обратимость во времени и парабола стационарных ворот с периодом возврата $1024$.
5. **[`WorldTrajectory.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/WorldTrajectory.lean)** — Трёхмерный мировой оператор эволюции поля $\Psi^{(t+1)} = \mathcal{G}_3(\Psi^{(t)})$, перепись 86 вихревых плакетов на такте $t = 2$ и теоремы-абляции знаменателя и деления `fdiv`.
6. **[`ContinuumPhysics.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/ContinuumPhysics.lean)** — Изотропный лапласиан $\Delta_{O_2}$, тензор деформаций, квантовый дефицит Бома, алгебра Паули — Клиффорда, $\alpha_{\mathrm{fs}}^{-1} \in \mathbb{Q}(\sqrt{2})$ и $587\times$ сжатие барьера.
7. **[`MendeleevPeriodicTable.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/MendeleevPeriodicTable.lean)** — Масштабная инвариантность $K^2$ и вывод 8 периодов таблицы Менделеева ($2, 8, 8, 18, 18, 32, 32, 50$).
8. **[`NuclearShells.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/NuclearShells.lean)** — Долина ядерной устойчивости, остров стабильности $N=184$, фазы ядерной пасты и несингулярное ядро компактного объекта ($833:1$).
9. **[`ParticleSpectrum.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/ParticleSpectrum.lean)** — 13-узловой ротор электрона, 6 ароматов кварков, калибровочные бозоны, адронные мультиплеты и полное квантование фазового пространства.
10. **[`ChemicalBonding.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/ChemicalBonding.lean)** — Ковалентная связь, закон Гесса, правила Вудворда — Хоффмана, катализ и граница Белла — Цирельсона $S_{\mathrm{QM}}^2 = (16/9)\,S_{\mathrm{LHV}}^2$.
11. **[`SuperconductorBioCad.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/SuperconductorBioCad.lean)** — Куперовское спаривание $2e$, критические температуры сверхпроводников (`TiNi`, `MgB₂`, купраты) и клеточный био-САПР.
12. **[`CosmologyHalo.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/CosmologyHalo.lean)** — Вакуумное гало голономии $16/3$ и плоские кривые вращения галактик без тёмной материи.
13. **[`PlanetogenesisAllometry.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/PlanetogenesisAllometry.lean)** — 6 зон протопланетного диска, отбор биометаллов, аллометрия Клейбера $3/4$ и 3 атмосферных фотонных окна.
14. **[`OntogenyMutagenesis.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/OntogenyMutagenesis.lean)** — Гомоморфизм марковского одеяла среды в геном, мутагенез `CpG` и обратный компилятор фенотипа.
15. **[`ReversibleComputing.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/ReversibleComputing.lean)** — Баллистический шаг без тепла Ландауэра, правило Борна, редукция 3-SAT, синдромная телепортация и 81-ричный фазовый модем.
16. **[`RotatorQuadratureCarrier.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/RotatorQuadratureCarrier.lean)** — Квадратуры на носителе и теорема внутреннего наблюдателя.
17. **[`HardwarePhotovoltaics.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/HardwarePhotovoltaics.lean)** — Барьер демона Лапласа, бабочка Грея, 4-канальный томограф фон Неймана и бесфононный кремниевый фотокаскад.
18. **[`MechanicsElasticity.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/MechanicsElasticity.lean)** & **[`LagrangianHamiltonian.lean`](https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/LagrangianHamiltonian.lean)** — 4 режима упругости, масштабирование порогов 8 металлов ($\sigma_{-1}=5E/8192$, Эшби $\sigma_{\mathrm{B}}=E/512$, скорость удара фон Кармана $v_{\mathrm{Karman}}=c_s/256$, ветвление трещины Йеффе $\frac{3}{8}c_s$), полевой Лагранжиан $\mathcal{L}_{\mathrm{world}}$, Гамильтониан $\mathcal{H}_{\mathrm{world}}$, 13-узловая причинная звезда $\mathcal{C}_{13}$ и тетраэдральное действие Верле.

---

## 4. Воспроизведение полной сборки `81/81` в Lean 4

```bash
cd lean
lake build
```

Ожидаемый финальный вывод:
```text
✔ [79/81] Built MtCarrier
Build completed successfully (81 jobs).
```
