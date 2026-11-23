# Серия «Дискретная квантовая механика в двух словах» (Fields Not Included)

Семантические тома (не `main`, не `vol-I`). SSOT формул: `model/`.

## Принципы (мета)

1. **construction** включает **matter** (`05-matter`) — механика ячейки и вход в T; без этого нет лестницы.
2. **Физика дальше дробится** по мере копания (новые тома, когда появляется **свой класс критических экспериментов**, а не «ещё одна глава»).
3. **Каждый том заканчивается блоком «Критические эксперименты»** — предсказание + что считается провалом модели; без этого мало смысла. Шаблоны: `sources/volumes/chapter-critical-experiments-<id>.tex`.
4. **§4.8 (системные кванты):** алгебра fractal в construction / macro; узел наблюдателя, **R_eff**, сравнение видов — том **observer**.
5. **Вычислительная лаборатория** — `computational-laboratory.tex`; журнал CE в `sources/lab-journal/*.tex` (ручной \LaTeX{}, четыре `\subsubsection*`). Обёртка: `labrecord` / `labseries` только дают заголовок и `\input`.
6. **Обработка результатов измерений** — `measurement-processing.tex` через `include-measurement-processing.tex` **в каждом томе** после гл. лаборатории, перед «Критическими экспериментами». GUM, Стьюдент, $E_n$.
7. **Критические эксперименты** — не буллет-лист: `\input{volumes/lab-*-records.tex}` с полными постановками (construction: `lab-construction-records.tex`; floors: `lab-floors-records.tex`).

## 1. Четыре основные книги единого Естествознания (`book/out/pdf/`)

| ID (`-Volume`) | Книга и назначение | `main-*.tex` | PDF `out/pdf/` |
|----|------------|--------------|------------|
| **monograph** | **Книга I. Теория:** Формальные основания ДКМ в Lean 4, ротатор на $\mathbb{Z}_{512}$, НКМ, Максвелл, $\alpha_{\mathrm{fs}}^{-1}$, оболочки $O_2(3)$, биофизика и предел $\lim M_n = \mathcal{M}$ | `main-monograph.tex` | `formal-foundations-monograph.pdf` |
| **laboratory** | **Книга II. Лаборатория:** Протокол чистой комнаты для кремниевого фотокаскада $441\text{ нм} \to 2\times 882\text{ нм} < 1107\text{ нм}$, A/B-тест Паули, сигнатуры `M1`–`M4`, матрица `F1`–`F6` и реестр критических экспериментов | `main-laboratory.tex` | `dqm-laboratory-manual.pdf` |
| **engineering** | **Книга III. Инженерия:** Теоретическая электротехника фазовой эстафеты ($V=\mathcal{C}_3, I=\mathcal{S}_3$), беспульсационные квадратурные выпрямители, вычисления без тепла Ландауэра, стек `Ring9 / Bus36 / VerletCell72` и 12-лучевые резонаторы $O_2(3)$ | `main-engineering.tex` | `dqm-engineering-handbook.pdf` |
| **course** | **Книга IV. Научно-популярный путеводитель (*Powered by Dr. STONE — 10,000,000,000%*):** Полный разговорный курс и дорожная карта крафта Вселенной от $1+2^3=3^2$ до живой клетки и кремния | `main-course.tex` | `natural-sciences-course.pdf` |

## 2. Серия «Как это создавалось» (Making-Of: 8-томная хроника объединения наук, `book/out/pdf/making-of/`)

| ID (`-Volume`) | Содержание | `main-*.tex` | PDF `out/pdf/making-of/` |
|----|------------|--------------|------------|
| **construction** | Построение: спуск, **g**, macro, **matter**, **α**, SI-лестница | `main-construction.tex` | `making-of/construction.pdf` |
| **floors** | Этажи 0–2 (отдельно от построения) | `main-floors.tex` | `making-of/floors.pdf` |
| **cosmology** | BB, CMB, `N_tick`, META §3 | `main-cosmology.tex` | `making-of/cosmology.pdf` |
| **observer** | Узел (M, R_eff), ε, τ_frame | `main-observer.tex` | `making-of/observer.pdf` |
| **chemistry** | Химия / физ. химия на T | `main-chemistry.tex` | `making-of/chemistry.pdf` |
| **biology** | Биология, генетический код, фолдинг и онтогенез на решётке ГЦК | `main-biology.tex` | `making-of/biology.pdf` |
| **compute** | Вычислительная архитектура под **g** | `main-compute.tex` | `making-of/compute.pdf` |
| **applied** | Прикладная механика кубооктаэдра и фазовые технологии (R&D): 12-лучевой концентратор ($25\times\text{--}587\times$), фазовый храповик $-1$ тик, 4-канальная голономная томография и геодинамо ядер | `main-applied.tex` | `making-of/applied.pdf` |

## Сборка

```powershell
cd book
./build.ps1                          # construction (default); xelatex+biber until refs/cites resolve
./build.ps1 -Volume floors   # prebuild construction → generated/construction-vol-refs.tex
./build.ps1 -Volume cosmology
```

`build.ps1` гоняет XeLaTeX столько раз, сколько нужно (до стабилизации ссылок в `.log`), с повторным `biber` при undefined citations. Межтомные номера: `generated/construction-vol-refs.tex` (для **floors**, макросы `\bcref`/`\bref`) и `generated/floors-vol-refs.tex` (для **construction**, `\fcref`/`\fvolrefs`); сборка **construction** при необходимости сначала гоняет **floors** (и наоборот), без рекурсии — флаги `-SkipFloorsPrebuild` / `-SkipConstructionPrebuild`.

Перед сборкой **construction**: `scripts/gen_lab_records_tex.py` → только `generated/lab-si-pdg-table.tex` (сводка модель/PDG). **Журнал CE** (постановка, ход, анализ, погрешность) --- `book/sources/lab-journal/*.tex`, правка вручную после прогона verify.

`-Volume`: `construction` | `floors` | `cosmology` | `observer` | `chemistry` | `biology` | `compute` | `applied`

## construction — главы

`volumes/vol-construction-body.tex`: `00-descent` … `06-si-sm`, **вычисл. лаборатория**, **обработка измерений**, **журнал CE-M**, приложение CA.

**Не входит:** этажи 0–2 → `floors`; нарратив наблюдателя → `observer`.

## floors — главы

`volumes/vol-floors-body.tex`: `09-floors-preface` … `12-floor2`, **лаборатория**, **метрология**, **журнал CE-F / CE-A**.

Граница с construction может сдвигаться; новые rung’и — расширение этого тома или новый том по правилу (3).

## Остальные тома

Заготовки в `volumes/vol-<id>-body.tex`; при наполнении — финальная глава критических экспериментов по тому же шаблону.

## Глоссарий

`sources/notation.tex`, `sources/glossary/` — общий; при конфликте побеждает `model/`.
