#!/usr/bin/env python3
"""
SSOT Book Exporter: Compiles all 5 core books from LaTeX SSOT (`book/sources/`)
into full chapter-by-chapter MkDocs Material pages (`docs/books/<book_slug>/`).

Rules enforced:
  1. Pure human prose & math in chapter body (zero inline code identifiers or `.lean` paths).
  2. All companion code links extracted to bottom collapsible "Code Located In" card.
  3. Zero stray LaTeX backslashes (`\\,`, `\\ `, `\\%`, `\\small`, `\\footnotesize`) outside math.
  4. Zero "communal apartment" walls of text: multi-step inline formula chains and dense
     multi-sentence paragraphs are automatically unpacked into airy paragraphs and display blocks.
  5. Real `$ ... $` formulas preserved in sidebar navigation for MathJax rendering.
"""

from __future__ import annotations

import re
import shutil
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BOOK_SOURCES = REPO_ROOT / "book" / "sources"
DOCS_BOOKS = REPO_ROOT / "docs" / "books"

BRACE4 = r"(?:[^{}]|\{(?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*\})*"

BOOKS = [
    {
        "slug": "book1-monograph",
        "entry": "volumes/vol-formal-foundations-monograph.tex",
        "pdf": "formal-foundations-monograph.pdf",
        "blueprint": "blueprint-book1",
        "title_ru": "Книга I. Формальные основания (Монография)",
        "title_en": "Book I. Formal Foundations (Monograph)",
    },
    {
        "slug": "book2-laboratory",
        "entry": "volumes/vol-laboratory-manual.tex",
        "pdf": "dqm-laboratory-manual.pdf",
        "blueprint": "blueprint-book2",
        "title_ru": "Книга II. Лабораторный практикум",
        "title_en": "Book II. Laboratory & Simulation Manual",
    },
    {
        "slug": "book3-engineering",
        "entry": "volumes/vol-engineering-handbook.tex",
        "pdf": "dqm-engineering-handbook.pdf",
        "blueprint": "blueprint-book3",
        "title_ru": "Книга III. Инженерный справочник",
        "title_en": "Book III. Engineering & Applied Design Handbook",
    },
    {
        "slug": "book4-course",
        "entry": "volumes/vol-natural-sciences-course.tex",
        "pdf": "natural-sciences-course.pdf",
        "blueprint": "blueprint-book4",
        "title_ru": "Книга IV. Курс единого естествознания",
        "title_en": "Book IV. Unified Natural Sciences Course",
    },
    {
        "slug": "book5-mathematics",
        "entry": "volumes/vol-projective-manifold-mathematics.tex",
        "pdf": "projective-manifold-mathematics.pdf",
        "blueprint": "blueprint-book5",
        "title_ru": "Книга V. Математика проективного многообразия",
        "title_en": "Book V. Projective Manifold Mathematics",
    },
]

CONSTRUCTIVE_MODULES = {
    "AxiomGuard.lean",
    "BipyramidGeometry.lean",
    "RotatorQuadrature.lean",
    "LogicCohomology.lean",
    "PillaiDiophantine.lean",
    "AbcPlanetaryWronskian.lean",
    "ModelTheoreticLimit.lean",
    "CollatzPlanetarySplice.lean",
    "RiemannHolonomy.lean",
    "RotatorCalculusPaper.lean",
}


def expand_inputs(rel_path: str) -> str:
    clean_rel = rel_path.strip()
    p = BOOK_SOURCES / clean_rel
    if not p.exists() and not clean_rel.endswith(".tex"):
        p = BOOK_SOURCES / (clean_rel + ".tex")
    if not p.exists():
        return ""
    text = p.read_text(encoding="utf-8")
    lines = []
    for line in text.splitlines():
        if line.lstrip().startswith("%"):
            continue
        line = re.sub(r"(?<!\\)%.*$", "", line)
        lines.append(line)
    joined = "\n".join(lines)
    return re.sub(r"\\input\{([^}]+)\}", lambda m: expand_inputs(m.group(1)), joined)


def unwrap_texorpdfstring(text: str) -> str:
    """Replace \\texorpdfstring{A}{B} with A (handles up to 4 levels of nested braces)."""
    pattern = re.compile(r"\\texorpdfstring\{(" + BRACE4 + r")\}\{(" + BRACE4 + r")\}")
    prev = None
    while prev != text:
        prev = text
        text = pattern.sub(r"\1", text)
    return text


def replace_paired_command(text: str, cmd: str, wrapper_left: str, wrapper_right: str) -> str:
    """Replace \\cmd{content} with wrapper_left + content + wrapper_right supporting up to 4 nested braces."""
    pat = re.compile(r"\\" + cmd + r"\{(" + BRACE4 + r")\}")
    prev = None
    while prev != text:
        prev = text
        text = pat.sub(lambda m: f"{wrapper_left}{m.group(1)}{wrapper_right}", text)
    return text


def extract_companion_code(raw_tex: str) -> tuple[list[str], list[str]]:
    cleaned = re.sub(r"\\allowbreak\s*", "", raw_tex)
    texttt_inner_pat = r"(?:\\\{|\\\}|[^{}])*"
    tokens = re.findall(r"\\texttt\{(" + texttt_inner_pat + r")\}", cleaned)
    for lean_arg in re.findall(r"\\lean\{([^}]*)\}", cleaned):
        for item in lean_arg.split(","):
            tokens.append(item.strip())

    modules: list[str] = []
    theorems: list[str] = []

    ignore_tokens = {
        "0 sorryAx", "0 Classical.choice", "0", "56/56", "68/68",
        "fdiv", "tdiv", "Int.fdiv", "Int.tdiv", "isZeroNat",
        "true", "false", "if", "NOT", "XOR", "OR", "AND", "ATG", "CpG",
        "M1", "M2", "M3", "M4", "F1", "F2", "F3", "F4", "F5", "F6",
        "CE-M", "CE-F", "CE-A", "CE-RD", "S", "MODEL",
        "Ring9", "Bus36", "VerletCell72", "Ring9/Bus36/VerletCell72",
        "signedOctants", "cellBranchingStates", "axisTransitionPairs",
    }

    for raw_tok in tokens:
        tok = raw_tok.replace(r"\_", "_").strip()
        tok = re.sub(r"\s+", " ", tok)
        if not tok or tok in ignore_tokens or tok.endswith(".pdf") or tok.endswith(".tex"):
            continue
        if ".lean" in tok or ".py" in tok or ".v" in tok:
            if tok not in modules:
                modules.append(tok)
        elif ("_" in tok or any(c.isupper() for c in tok[1:])) and re.match(r"^[a-zA-Z0-9_. ]+$", tok):
            base_id = tok.split()[0]
            if len(base_id) >= 4 and base_id not in ignore_tokens and base_id not in theorems:
                theorems.append(base_id)

    return modules, theorems


def format_module_link(mod: str) -> str:
    clean = mod.strip().strip("/")
    basename = clean.split("/")[-1]
    if basename in CONSTRUCTIVE_MODULES:
        url = f"https://github.com/AI-Guiders/dqm-lean/blob/main/Constructive/{basename}"
        return f"[`Constructive/{basename}`]({url})"
    if basename.endswith(".lean"):
        url = f"https://github.com/AI-Guiders/dqm-lean/blob/main/MtCarrier/{basename}"
        return f"[`MtCarrier/{basename}`]({url})"
    return f"`{clean}`"


def build_companion_code_footer(
    modules: list[str], theorems: list[str], blueprint_id: str, lang: str = "ru"
) -> str:
    bp_url = f"https://ai-guiders.github.io/discrete-quantum-mechanics/{blueprint_id}/"
    graph_url = f"https://ai-guiders.github.io/discrete-quantum-mechanics/{blueprint_id}/dep_graph_document.html"
    mod_links = []
    for m in modules:
        lnk = format_module_link(m)
        if lnk not in mod_links:
            mod_links.append(lnk)

    if lang == "ru":
        lines = [
            "\n\n---\n",
            '??? abstract "Сопроводительный код и Lean 4 Blueprint к главе (Code Located In)"',
            f"    - **Интерактивный Lean 4 Blueprint и граф теорем тома:** [Открыть Blueprint (`L∃∀N`)]({bp_url}) · [Интерактивный граф зависимостей]({graph_url})",
        ]
        if mod_links:
            lines.append("    - **Файлы и модули верификации:** " + ", ".join(mod_links))
        if theorems:
            thm_list = ", ".join(f"`{t}`" for t in theorems)
            lines.append("    - **Верифицированные теоремы и операторы:** " + thm_list)
        return "\n".join(lines) + "\n"
    else:
        lines = [
            "\n\n---\n",
            '??? abstract "Companion Code & Lean 4 Blueprint (Code Located In)"',
            f"    - **Interactive Lean 4 Blueprint & Theorem Graph:** [Open Blueprint (`L∃∀N`)]({bp_url}) · [Interactive Dependency Graph]({graph_url})",
        ]
        if mod_links:
            lines.append("    - **Verification Modules & Files:** " + ", ".join(mod_links))
        if theorems:
            thm_list = ", ".join(f"`{t}`" for t in theorems)
            lines.append("    - **Verified Theorems & Operators:** " + thm_list)
        return "\n".join(lines) + "\n"


def purify_prose_and_math(text: str) -> str:
    # 0. Remove authoring section "Как вести этот раздел" and leanblueprint tags (\lean, \leanok, \uses)
    text = re.sub(r"\\section\{Как вести этот раздел\}[\s\S]*?\\end\{labrecord\}", "", text)
    text = re.sub(r"\\(?:lean|uses|proves|discussion)\{[^}]*\}\s*", "", text)
    text = re.sub(r"\\(?:leanok|mathlibok|notready)\b\s*", "", text)

    # 1. Strip \allowbreak and normalize \~{} -> ~
    text = re.sub(r"\\allowbreak\s*", "", text)
    text = text.replace(r"\~{}", "~")

    # 2. Normalize \texttt{...} arguments
    texttt_inner_pat = r"(?:\\\{|\\\}|[^{}])*"

    def normalize_texttt_arg(m: re.Match) -> str:
        inner = m.group(1)
        inner = inner.replace(r"\_", "_").replace(r"\&", "&")
        inner = inner.replace(r"\{", "(").replace(r"\}", ")")
        inner = re.sub(r"\\textbackslash\s*", r"\\", inner)
        inner = inner.replace(r"\ {}", "~")
        inner = re.sub(r"\s+", " ", inner).strip()
        return r"\texttt{" + inner + "}"

    text = re.sub(r"\\texttt\{(" + texttt_inner_pat + r")\}", normalize_texttt_arg, text)

    # 3. Strip standalone "Формальная верификация: ..." paragraphs
    text = re.sub(r"\\emph\{Формальная верификация:\}[^\n]+\n?", "", text)

    # 4. Replace code function names inside math with pure mathematical symbols first
    in_math_replacements = {
        r"\texttt{signedOctants}": r"\mathcal{O}_{\mathrm{oct}}",
        r"\texttt{cellBranchingStates}": r"\mathcal{B}_{\mathrm{cell}}",
        r"\texttt{axisTransitionPairs}": r"\mathcal{A}_{\mathrm{axis}}",
    }
    for old_tok, new_math in in_math_replacements.items():
        text = text.replace(old_tok, new_math)

    # 5. Strip parenthetical blocks that contain any \texttt{...} code reference
    text = re.sub(r"\s*\((?:[^()]*?\\texttt\{[^{}]*\}[^()]*)\)", "", text)

    # 6. Replace remaining prose code tokens with clean Russian mathematical prose
    prose_replacements = {
        r"\texttt{Ring9/Bus36/VerletCell72}": "9/36/72-битного регистра Верле",
        r"\texttt{Ring9}": r"$\mathbb{Z}_{512}$",
        r"\texttt{Bus36}": "36-битной шины полушага",
        r"\texttt{VerletCell72}": "72-битной ячейки Верле",
        r"\texttt{Int.fdiv}": r"$\lfloor\cdot\rfloor$",
        r"\texttt{fdiv}": r"$\lfloor\cdot\rfloor$",
        r"\texttt{Int.tdiv}": r"$\operatorname{trunc}(\cdot)$",
        r"\texttt{tdiv}": r"$\operatorname{trunc}(\cdot)$",
        r"\texttt{isZeroNat}": r"$\delta_{k,0}$",
        r"\texttt{denomRaw.toNat}": r"$\max(D_{\mathrm{raw}}, 0)$",
    }
    for old_tok, new_prose in prose_replacements.items():
        text = text.replace(old_tok, new_prose)

    # 7. Strip inline phrases referencing Lean theorems/modules in prose
    text = re.sub(r"\s*в модулях\s+\\texttt\{[^{}]*\}\s+и\s+\\texttt\{[^{}]*\}", "", text)
    text = re.sub(r"\s*в модуле\s+\\texttt\{[^{}]*\}", "", text)
    text = re.sub(r"\s*в каталоге\s+\\texttt\{[^{}]*\}", "", text)
    text = re.sub(r"теоремы\s+\\texttt\{[^{}]*\}", "теоремы", text)
    text = re.sub(r"теорема\s+\\texttt\{[^{}]*\}", "теорема", text)
    text = re.sub(r"оператор\s+\\texttt\{[^{}]*\}", "оператор", text)

    def texttt_to_clean_prose(m: re.Match) -> str:
        val = m.group(1).strip()
        if ".lean" in val or ".pdf" in val or ".py" in val or val.count("_") >= 2:
            return ""
        return f"**{val}**" if val in ("NOT", "XOR", "OR", "AND", "ATG", "CpG") else val

    text = re.sub(r"\\texttt\{([^{}]*)\}", texttt_to_clean_prose, text)
    return text


def clean_prose_outside_math_and_unpack_walls(text: str) -> str:
    """
    1. Split text by math blocks (`$$...$$` and `$...$`).
    2. In non-math prose chunks:
       - Remove all LaTeX spacing/escaping backslashes (`\\,`, `\\ `, `\\;`, `\\:`, `\\!`, `\\%`, `\\&`, `\\dots`, `\\LaTeX`).
       - Break dense wall-of-text paragraphs at natural logical transitions so every paragraph breathes.
    3. For long inline math chains (`$...$` with >= 2 relational operators and length >= 45 chars),
       give them breathing room so they don't pack into a cramped wall of text.
    """
    math_token_pat = re.compile(r"(\$\$[\s\S]*?\$\$|\$[^$\n]+\$)")
    parts = math_token_pat.split(text)

    cleaned_parts: list[str] = []
    for idx, part in enumerate(parts):
        if idx % 2 == 1:
            # Math block ($...$ or $$...$$)
            if part.startswith("$") and not part.startswith("$$"):
                inner = part[1:-1].strip()
                rel_count = len(
                    re.findall(r"(?:=|\\ge|\\le|\\equiv|\\implies|\\iff|\\approx|<|>)", inner)
                )
                # If it's a long multi-step derivation chain (like the induction step in the screenshot),
                # put it on its own centered display line if at top level, or surround with line breaks
                if len(inner) >= 48 and rel_count >= 3:
                    cleaned_parts.append(f"\n\n$$\n{inner}\n$$\n\n")
                    continue
            cleaned_parts.append(part)
        else:
            # Prose chunk outside math!
            p = part
            p = p.replace(r"\,", " ")
            p = p.replace(r"\;", " ")
            p = p.replace(r"\:", " ")
            p = p.replace(r"\!", "")
            p = re.sub(r"\\\s+", " ", p)
            p = p.replace(r"\%", "%")
            p = p.replace(r"\&", "&")
            p = p.replace(r"\#", "#")
            p = p.replace(r"\_", "_")
            p = re.sub(r"\\LaTeX(?:\{\})?", "LaTeX", p)
            p = re.sub(r"\\(?:dots|ldots)(?:\{\})?", "…", p)
            p = re.sub(r"\\(?:small|footnotesize|large|Large|sloppy|par|quad|qquad)\b\s*", " ", p)
            cleaned_parts.append(p)

    joined = "".join(cleaned_parts)

    # Unpack dense "communal apartment" paragraphs: insert a paragraph break (preserving indentation)
    # before logical transition sentences inside long paragraphs.
    transitions = (
        r"При \$\\mathbf\{d = 3\}\$",
        r"Тем самым ",
        r"Следовательно, ",
        r"Подстановка ",
        r"В частности, ",
        r"Напротив, ",
        r"Отсюда ",
        r"При этом ",
        r"В результате ",
        r"С другой стороны, ",
        r"Таким образом, ",
    )
    trans_rx = re.compile(r"([.!?])\s+(" + "|".join(transitions) + r")")

    out_lines: list[str] = []
    for line in joined.splitlines():
        # Only split prose lines that are long (> 220 chars) and not table rows or headings
        stripped = line.lstrip()
        if len(stripped) > 220 and not stripped.startswith(("|", "#", "!", "?", "$$")):
            indent = line[: len(line) - len(stripped)]
            expanded = trans_rx.sub(lambda m: f"{m.group(1)}\n\n{indent}{m.group(2)}", line)
            out_lines.append(expanded)
        else:
            out_lines.append(line)

    return "\n".join(out_lines)


def convert_tabular(match: re.Match) -> str:
    body = match.group(1)
    body = re.sub(r"\\(?:toprule|midrule|bottomrule|hline|addlinespace(?:\[[^\]]*\])?)", "", body)
    raw_rows = [r.strip() for r in body.split(r"\\") if r.strip()]
    if not raw_rows:
        return ""
    parsed_rows = []
    for r in raw_rows:
        cells = [c.strip().replace("\n", " ") for c in r.split("&")]
        if any(cells):
            parsed_rows.append(cells)
    if not parsed_rows:
        return ""
    ncol = max(len(r) for r in parsed_rows)
    norm_rows = [r + [""] * (ncol - len(r)) for r in parsed_rows]
    header = "| " + " | ".join(norm_rows[0]) + " |"
    sep = "| " + " | ".join(["---"] * ncol) + " |"
    lines = [header, sep]
    for r in norm_rows[1:]:
        lines.append("| " + " | ".join(r) + " |")
    return "\n\n" + "\n".join(lines) + "\n\n"


def convert_lists(text: str) -> str:
    text = re.sub(r"\\begin\{(enumerate|itemize|description)\}\s*\[[^\]]*\]", r"\\begin{\1}", text)

    lines = text.splitlines()
    out_lines: list[str] = []
    stack: list[str] = []
    enum_counters: list[int] = []

    for line in lines:
        stripped = line.strip()
        m_begin = re.match(r"^\\begin\{(enumerate|itemize|description)\}(.*)$", stripped)
        if m_begin:
            kind = m_begin.group(1)
            rest = m_begin.group(2).strip()
            if out_lines and out_lines[-1].strip() != "":
                out_lines.append("")
            stack.append(kind)
            enum_counters.append(0)
            if rest:
                out_lines.append("    " * len(stack) + rest)
            continue

        m_end = re.match(r"^\\end\{(enumerate|itemize|description)\}(.*)$", stripped)
        if m_end:
            if stack:
                stack.pop()
                enum_counters.pop()
            if out_lines and out_lines[-1].strip() != "":
                out_lines.append("")
            rest = m_end.group(2).strip()
            if rest:
                out_lines.append("    " * len(stack) + rest)
            continue

        if stack and stripped.startswith(r"\item"):
            indent = "    " * (len(stack) - 1)
            kind = stack[-1]
            rest = stripped[len(r"\item"):].strip()
            if out_lines and out_lines[-1].strip() != "":
                out_lines.append("")
            m_opt = re.match(r"^\[((?:[^\[\]]|\[[^\[\]]*\])*)\]\s*(.*)$", rest)
            if m_opt and kind != "enumerate":
                label_txt = m_opt.group(1).strip()
                item_body = m_opt.group(2).strip()
                out_lines.append(f"{indent}- **{label_txt}** {item_body}")
            else:
                if m_opt:
                    rest = m_opt.group(2).strip()
                if kind == "enumerate":
                    enum_counters[-1] += 1
                    idx = enum_counters[-1]
                    out_lines.append(f"{indent}{idx}. {rest}")
                else:
                    out_lines.append(f"{indent}- {rest}")
        else:
            if stack:
                if stripped == "":
                    out_lines.append("")
                else:
                    indent = "    " * len(stack)
                    out_lines.append(f"{indent}{stripped}")
            else:
                out_lines.append(line)

    return "\n".join(out_lines)


def convert_admonition_envs(text: str) -> str:
    env_map = {
        "theorem": ("note", "Теорема"),
        "definition": ("info", "Определение"),
        "remark": ("tip", "Замечание"),
        "proof": ("success", "Доказательство"),
    }

    for env_name, (adm_type, title_prefix) in env_map.items():
        pattern = re.compile(
            r"\\begin\{" + env_name + r"\}(?:\[((?:[^\[\]]|\[[^\[\]]*\])*)\])?([\s\S]*?)\\end\{" + env_name + r"\}"
        )

        def repl(m: re.Match, adm_type=adm_type, title_prefix=title_prefix, env_name=env_name) -> str:
            opt_title = (m.group(1) or "").strip()
            body = m.group(2).strip()
            header_title = f"{title_prefix} ({opt_title})" if opt_title else title_prefix
            header_title = header_title.replace('"', "'")
            marker = "???+ " if env_name == "proof" else "!!! "
            indented = "\n".join("    " + ln if ln.strip() else "" for ln in body.splitlines())
            return f'\n\n{marker}{adm_type} "{header_title}"\n\n{indented}\n\n'

        text = pattern.sub(repl, text)

    return text


def latex_to_markdown(tex: str) -> str:
    text = tex

    # 1. Strip layout-only boilerplate
    text = re.sub(r"\\(?:markboth|addcontentsline)\{[^}]*\}\{[^}]*\}(?:\{[^}]*\})?", "", text)
    text = re.sub(r"\\(?:noindent|sloppy|bigskip|medskip|smallskip|centering)\b", "", text)
    text = re.sub(r"\\(?:vspace|setlength)\*?\{[^}]*\}(?:\{[^}]*\})?", "", text)
    text = re.sub(r"\\rule\{[^}]*\}\{[^}]*\}", "\n---\n", text)

    # 2. Expand semantic notation macros to their exact LaTeX symbols
    text = text.replace(r"\caSignalSpeed", "c_0")
    text = text.replace(r"\speedC", "c")
    text = text.replace(r"\geomNeighborTwelve", "N_{12}")
    text = text.replace(r"\phaseRingCount", r"N_{\mathrm{ring}}")
    text = text.replace(r"\caPlanckCell", "V_P")
    text = text.replace(r"\PlanckCell", "V_P")
    text = text.replace(r"\caStepSpace", "a")
    text = text.replace(r"\caStepTime", r"\Delta t")
    text = text.replace(r"\caKappaGeom", r"\kappa")
    text = text.replace(r"\latGCKshort", "ГЦК")
    text = re.sub(r"\\Axref\{ax:A([^}]+)\}", r"$A_{\1}$", text)

    # 3. Unwrap \texorpdfstring{math}{plain} -> math
    text = unwrap_texorpdfstring(text)

    # 4. Purify prose and math: remove all code identifiers/filenames from reading flow
    text = purify_prose_and_math(text)

    # 5. Lab environments -> sections/subsections
    text = re.sub(
        r"\\begin\{labseries\}\{(" + BRACE4 + r")\}\{([^}]*)\}",
        r"\\section{\1}",
        text,
    )
    text = re.sub(r"\\end\{labseries\}", "", text)
    text = re.sub(
        r"\\begin\{labrecord\}\{(" + BRACE4 + r")\}\{([^}]*)\}",
        r"\\subsection{\1}",
        text,
    )
    text = re.sub(r"\\end\{labrecord\}", "", text)

    # 6. Number equations per chapter and convert display math (`equation`, `align`, `\[...\]`) to $$ ... $$
    #    IMPORTANT: Strip blank lines inside `$$ ... $$` so pymdownx.arithmatex never aborts a math block!
    eq_counter = 0
    eq_labels: dict[str, int] = {}

    def wrap_display_math(m: re.Match) -> str:
        nonlocal eq_counter
        env = m.group(1)
        content = m.group(2).strip()
        found_labels = re.findall(r"\\label\{([^}]+)\}", content)
        content = re.sub(r"\\label\{([^}]+)\}", "", content).strip()
        non_empty_lines = [ln.strip() for ln in content.splitlines() if ln.strip()]
        content = "\n".join(non_empty_lines)
        tag_str = ""
        if found_labels:
            eq_counter += 1
            for lbl in found_labels:
                eq_labels[lbl] = eq_counter
            tag_str = f" \\tag{{{eq_counter}}}"
        if env in ("align", "align*"):
            return f"\n\n$$\n\\begin{{aligned}}\n{content}\n\\end{{aligned}}{tag_str}\n$$\n\n"
        return f"\n\n$$\n{content}{tag_str}\n$$\n\n"

    text = re.sub(
        r"\\begin\{(equation\*?|align\*?)\}([\s\S]*?)\\end\{\1\}",
        wrap_display_math,
        text,
    )

    def wrap_bracket_math(m: re.Match) -> str:
        content = m.group(1).strip()
        content = re.sub(r"\\label\{([^}]+)\}", "", content).strip()
        non_empty_lines = [ln.strip() for ln in content.splitlines() if ln.strip()]
        content = "\n".join(non_empty_lines)
        return f"\n\n$$\n{content}\n$$\n\n"

    text = re.sub(r"\\\[([\s\S]*?)\\\]", wrap_bracket_math, text)

    # 7. Convert typography dashes & ~ before tables so Markdown table separators `| --- |` are preserved
    text = text.replace("---", "—").replace("--", "–").replace("~", " ")

    # 8. Convert tables
    text = re.sub(r"\\begin\{table\}(?:\[[^\]]*\])?", "", text)
    text = re.sub(r"\\end\{table\}", "", text)
    text = re.sub(r"\\resizebox\{[^}]*\}\{[^}]*\}\{([\s\S]*?\\end\{tabular\})\s*\}", r"\1", text)
    text = re.sub(r"\\caption\{(" + BRACE4 + r")\}", r"\n*\1*\n", text)
    text = re.sub(
        r"\\begin\{tabular\}\{" + BRACE4 + r"\}([\s\S]*?)\\end\{tabular\}",
        convert_tabular,
        text,
    )

    # 9. Convert section headers
    text = re.sub(r"\\part\*?\{(" + BRACE4 + r")\}", r"\n## Часть: \1\n", text)
    text = re.sub(r"\\section\*?\{(" + BRACE4 + r")\}", r"\n## \1\n", text)
    text = re.sub(r"\\subsection\*?\{(" + BRACE4 + r")\}", r"\n### \1\n", text)
    text = re.sub(r"\\subsubsection\*?\{(" + BRACE4 + r")\}", r"\n#### \1\n", text)
    text = re.sub(r"\\paragraph\*?\{(" + BRACE4 + r")\}", r"\n**\1**\n", text)

    # 10. Convert inline formatting (\textbf, \emph, \textit, \url)
    text = replace_paired_command(text, "textbf", "**", "**")
    text = replace_paired_command(text, "emph", "*", "*")
    text = replace_paired_command(text, "textit", "*", "*")
    text = replace_paired_command(text, "url", "<", ">")

    # 11. Resolve cross-references (\eqref, \ref, \cref)
    text = re.sub(r"\\label\{[^}]+\}", "", text)

    def resolve_ref(m: re.Match) -> str:
        lbl = m.group(1).strip()
        if lbl in eq_labels:
            return f"({eq_labels[lbl]})"
        return ""

    text = re.sub(r"\\(?:eqref|ref|cref|bcref|CiteConstruction)\{([^}]+)\}", resolve_ref, text)

    # 12. Clean all stray LaTeX backslashes outside math AND unpack dense "communal apartment" paragraphs/chains
    text = clean_prose_outside_math_and_unpack_walls(text)

    # 13. Convert lists with 4-space indentation and blank-line separation
    text = convert_lists(text)

    # 14. Convert theorem/definition/remark/proof environments to MkDocs Admonitions
    text = convert_admonition_envs(text)
    text = re.sub(r"\\begin\{(?:center|quote)\}", "\n", text)
    text = re.sub(r"\\end\{(?:center|quote)\}", "\n", text)

    # 15. Final whitespace cleanup
    text = re.sub(r" +([,.;:])", r"\1", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip() + "\n"


def split_into_chapters(full_tex: str, default_title: str) -> list[tuple[str, str]]:
    full_tex = unwrap_texorpdfstring(full_tex)
    pattern = re.compile(r"\\chapter\*?\{((?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)\}")
    matches = list(pattern.finditer(full_tex))
    if not matches:
        return [(default_title, full_tex)]

    chapters: list[tuple[str, str]] = []
    prefix = full_tex[: matches[0].start()].strip()
    if prefix:
        chapters.append(("Введение", prefix))

    for idx, m in enumerate(matches):
        raw_title = unwrap_texorpdfstring(m.group(1)).strip()
        raw_title = purify_prose_and_math(raw_title).strip()
        raw_title = replace_paired_command(raw_title, "textbf", "", "")
        raw_title = replace_paired_command(raw_title, "emph", "", "")
        raw_title = raw_title.replace("---", "—").replace("--", "–").replace("~", " ")
        raw_title = clean_prose_outside_math_and_unpack_walls(raw_title).strip()
        start = m.end()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(full_tex)
        body = full_tex[start:end].strip()
        chapters.append((raw_title, body))

    return chapters


def format_nav_title_with_math(title: str) -> str:
    """
    Preserve `$ ... $` formulas inside sidebar labels so MathJax typesets them cleanly
    in the left sidebar! Escape `\\` -> `\\\\` and `"` -> `'` for YAML double-quoted strings.
    """
    s = re.sub(r"\s+", " ", title).strip()
    s = s.replace('"', "'")
    s = s.replace("\\", "\\\\")
    return s


def main() -> None:
    if DOCS_BOOKS.exists():
        shutil.rmtree(DOCS_BOOKS)
    DOCS_BOOKS.mkdir(parents=True, exist_ok=True)

    nav_books_en = []
    nav_books_ru_translations: dict[str, str] = {}

    total_chapters = 0
    for book in BOOKS:
        slug = book["slug"]
        book_dir = DOCS_BOOKS / slug
        book_dir.mkdir(parents=True, exist_ok=True)

        full_tex = expand_inputs(book["entry"])
        chapters = split_into_chapters(full_tex, book["title_ru"])

        book_nav_items = []
        for idx, (ch_title, ch_body) in enumerate(chapters, start=1):
            total_chapters += 1
            ch_file_stem = f"ch{idx:02d}"

            modules, theorems = extract_companion_code(ch_body)
            md_body = latex_to_markdown(ch_body)

            footer_ru = build_companion_code_footer(
                modules, theorems, book["blueprint"], lang="ru"
            )
            footer_en = build_companion_code_footer(
                modules, theorems, book["blueprint"], lang="en"
            )

            header_ru = f"# {idx}. {ch_title}\n\n"
            header_en = f"# {idx}. {ch_title}\n\n"

            (book_dir / f"{ch_file_stem}.ru.md").write_text(
                header_ru + md_body + footer_ru, encoding="utf-8", newline="\n"
            )
            (book_dir / f"{ch_file_stem}.md").write_text(
                header_en + md_body + footer_en, encoding="utf-8", newline="\n"
            )

            nav_label = format_nav_title_with_math(f"{idx}. {ch_title}")
            book_nav_items.append((nav_label, f"books/{slug}/{ch_file_stem}.md"))

        nav_books_en.append((book["title_en"], book["title_ru"], book_nav_items))
        nav_books_ru_translations[book["title_en"]] = book["title_ru"]

    mkdocs_yml = REPO_ROOT / "mkdocs.yml"
    yml_text = mkdocs_yml.read_text(encoding="utf-8")

    trans_lines = [
        "          nav_translations:",
        "            Overview & 5 Books: Обзор и 5 книг",
        "            For Engineers, Shipbuilders & CAD: Инженерам, корабелам и САПР",
        "            For Mathematicians & Lean 4: Математикам и Lean 4",
        "            For Physicists & Natural Science: Физикам и естествоиспытателям",
    ]
    for title_en, title_ru in nav_books_ru_translations.items():
        trans_lines.append(f'            "{title_en}": "{title_ru}"')

    nav_lines = [
        "nav:",
        "  - Overview & 5 Books: index.md",
        "  - For Engineers, Shipbuilders & CAD: engineering.md",
        "  - For Mathematicians & Lean 4: mathematics.md",
        "  - For Physicists & Natural Science: physics.md",
    ]
    for title_en, _title_ru, items in nav_books_en:
        nav_lines.append(f'  - "{title_en}":')
        for label, rel_md in items:
            nav_lines.append(f'      - "{label}": {rel_md}')

    yml_text = re.sub(
        r"          nav_translations:[\s\S]*?(?=\n\nmarkdown_extensions:)",
        lambda _m: "\n".join(trans_lines),
        yml_text,
    )
    yml_text = re.sub(
        r"nav:[\s\S]*$",
        lambda _m: "\n".join(nav_lines) + "\n",
        yml_text,
    )
    mkdocs_yml.write_text(yml_text, encoding="utf-8", newline="\n")

    print(f"Exported {len(BOOKS)} full books ({total_chapters} chapters) from book/sources/ SSOT to docs/books/.")


if __name__ == "__main__":
    main()
