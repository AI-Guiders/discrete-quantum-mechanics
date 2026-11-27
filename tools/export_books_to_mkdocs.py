#!/usr/bin/env python3
"""
SSOT Book Exporter: Compiles all 5 core books from LaTeX SSOT (`book/sources/`)
into full chapter-by-chapter MkDocs Material pages (`docs/books/<book_slug>/`).

Rule:
  - The chapter body is 100% pure human text and mathematical notation (zero code
    identifiers, zero `.lean`/`.py` paths or `snake_case`/`camelCase` tokens in the reading flow).
  - All Lean 4 modules, theorem names, and verification scripts referenced in the LaTeX SSOT
    are automatically extracted into a collapsible "💿 Сопроводительный код главы (Code Located In)"
    card at the bottom of the chapter (like the companion CD-ROM of a book).
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
        "title_ru": "Книга I. Формальные основания (Монография)",
        "title_en": "Book I. Formal Foundations (Monograph)",
    },
    {
        "slug": "book2-laboratory",
        "entry": "volumes/vol-laboratory-manual.tex",
        "pdf": "dqm-laboratory-manual.pdf",
        "title_ru": "Книга II. Лабораторный практикум",
        "title_en": "Book II. Laboratory & Simulation Manual",
    },
    {
        "slug": "book3-engineering",
        "entry": "volumes/vol-engineering-handbook.tex",
        "pdf": "dqm-engineering-handbook.pdf",
        "title_ru": "Книга III. Инженерный справочник",
        "title_en": "Book III. Engineering & Applied Design Handbook",
    },
    {
        "slug": "book4-course",
        "entry": "volumes/vol-natural-sciences-course.tex",
        "pdf": "natural-sciences-course.pdf",
        "title_ru": "Книга IV. Курс единого естествознания",
        "title_en": "Book IV. Unified Natural Sciences Course",
    },
    {
        "slug": "book5-mathematics",
        "entry": "volumes/vol-projective-manifold-mathematics.tex",
        "pdf": "projective-manifold-mathematics.pdf",
        "title_ru": "Книга V. Математика проективного многообразия",
        "title_en": "Book V. Projective Manifold Mathematics",
    },
]

# Known Lean modules in dqm-lean for clickable links in "Code Located In"
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
        # Strip trailing unescaped LaTeX comment %
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
    """
    Scan a chapter's raw LaTeX for all referenced Lean modules (.lean), code files,
    and formal theorem/operator identifiers so they can be placed in the bottom
    'Code Located In' card while keeping the chapter text 100% prose + math.
    """
    cleaned = re.sub(r"\\allowbreak\s*", "", raw_tex)
    texttt_inner_pat = r"(?:\\\{|\\\}|[^{}])*"
    tokens = re.findall(r"\\texttt\{(" + texttt_inner_pat + r")\}", cleaned)

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


def build_companion_code_footer(modules: list[str], theorems: list[str], lang: str = "ru") -> str:
    if not modules and not theorems:
        return ""
    mod_links = []
    for m in modules:
        lnk = format_module_link(m)
        if lnk not in mod_links:
            mod_links.append(lnk)

    if lang == "ru":
        lines = [
            "\n\n---\n",
            '??? abstract "Сопроводительный код и формализация к главе (Code Located In)"',
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
            '??? abstract "Companion Code & Formalization (Code Located In)"',
        ]
        if mod_links:
            lines.append("    - **Verification Modules & Files:** " + ", ".join(mod_links))
        if theorems:
            thm_list = ", ".join(f"`{t}`" for t in theorems)
            lines.append("    - **Verified Theorems & Operators:** " + thm_list)
        return "\n".join(lines) + "\n"


def purify_prose_and_math(text: str) -> str:
    """
    Remove all code identifiers, filenames, and CLI commands from the narrative prose
    and mathematical formulas so the chapter reads as a pure book.
    """
    # 0. Remove internal authoring section "Как вести этот раздел" + template labrecord
    text = re.sub(
        r"\\section\{Как вести этот раздел\}[\s\S]*?\\end\{labrecord\}",
        "",
        text,
    )

    # 1. Strip \allowbreak and spaces immediately following it, and normalize \~{} -> ~
    text = re.sub(r"\\allowbreak\s*", "", text)
    text = text.replace(r"\~{}", "~")

    # 2. Normalize \texttt{...} arguments so we can match them cleanly
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

    # 6. Strip inline phrases referencing Lean theorems/modules in prose
    text = re.sub(r"\s*в модулях\s+\\texttt\{[^{}]*\}\s+и\s+\\texttt\{[^{}]*\}", "", text)
    text = re.sub(r"\s*в модуле\s+\\texttt\{[^{}]*\}", "", text)
    text = re.sub(r"\s*в каталоге\s+\\texttt\{[^{}]*\}", "", text)
    text = re.sub(r"теоремы\s+\\texttt\{[^{}]*\}", "теоремы", text)
    text = re.sub(r"теорема\s+\\texttt\{[^{}]*\}", "теорема", text)
    text = re.sub(r"оператор\s+\\texttt\{[^{}]*\}", "оператор", text)

    # 7. Convert any remaining \texttt{...} (such as biological codons ATG, CpG, logic gates NOT, XOR, AND)
    # into clean mathematical/roman text without code backticks!
    def texttt_to_clean_prose(m: re.Match) -> str:
        val = m.group(1).strip()
        # If it's a long snake_case/camelCase identifier or file path that survived outside parentheses, drop it
        if ".lean" in val or ".pdf" in val or ".py" in val or val.count("_") >= 2:
            return ""
        return f"**{val}**" if val in ("NOT", "XOR", "OR", "AND", "ATG", "CpG") else val

    text = re.sub(r"\\texttt\{([^{}]*)\}", texttt_to_clean_prose, text)
    return text


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
    """
    Convert itemize, enumerate, and description environments into properly spaced
    and 4-space-indented Markdown lists so Python-Markdown never glues items together.
    """
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
    """Convert theorem, definition, remark, proof environments to MkDocs admonitions."""
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

    # 2. Expand semantic notation macros to their exact LaTeX symbols (glossary/notation-entries.tex)
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
    eq_counter = 0
    eq_labels: dict[str, int] = {}

    def wrap_display_math(m: re.Match) -> str:
        nonlocal eq_counter
        env = m.group(1)
        content = m.group(2).strip()
        found_labels = re.findall(r"\\label\{([^}]+)\}", content)
        content = re.sub(r"\\label\{([^}]+)\}", "", content).strip()
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
        return f"\n\n$$\n{content}\n$$\n\n"

    text = re.sub(r"\\\[([\s\S]*?)\\\]", wrap_bracket_math, text)

    # 7. Convert typography dashes & ~ before tables so Markdown table separators `| --- |` are preserved
    text = text.replace("---", "—").replace("--", "–").replace("~", " ")

    # 8. Convert tables (`\begin{table}...\end{table}` and `\begin{tabular}{...}...\end{tabular}`)
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

    # 12. Convert lists with 4-space indentation and blank-line separation
    text = convert_lists(text)

    # 13. Convert theorem/definition/remark/proof environments to MkDocs Admonitions
    text = convert_admonition_envs(text)
    text = re.sub(r"\\begin\{(?:center|quote)\}", "\n", text)
    text = re.sub(r"\\end\{(?:center|quote)\}", "\n", text)

    # 14. Final whitespace cleanup
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
        start = m.end()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(full_tex)
        body = full_tex[start:end].strip()
        chapters.append((raw_title, body))

    return chapters


def clean_nav_label(title: str) -> str:
    """Create a clean sidebar label without raw LaTeX backslashes."""
    s = title
    s = re.sub(r"\\(?:mathbb|mathcal|mathrm|mathbf|operatorname)\{([^}]*)\}", r"\1", s)
    s = s.replace(r"\implies", "=>").replace(r"\iff", "<=>").replace(r"\to", "->")
    s = s.replace(r"\times", "×").replace(r"\cdot", "·").replace(r"\le", "≤").replace(r"\ge", "≥")
    s = re.sub(r"\\sqrt\{([^}]*)\}", r"sqrt(\1)", s)
    s = re.sub(r"\\([a-zA-Z]+)", r"\1", s)
    s = s.replace("\\", "").replace("$", "").replace("{", "").replace("}", "")
    s = re.sub(r"\s+", " ", s).strip()
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

            footer_ru = build_companion_code_footer(modules, theorems, lang="ru")
            footer_en = build_companion_code_footer(modules, theorems, lang="en")

            header_ru = f"# {ch_title}\n\n"
            header_en = f"# {ch_title}\n\n"

            (book_dir / f"{ch_file_stem}.ru.md").write_text(
                header_ru + md_body + footer_ru, encoding="utf-8", newline="\n"
            )
            (book_dir / f"{ch_file_stem}.md").write_text(
                header_en + md_body + footer_en, encoding="utf-8", newline="\n"
            )

            short_title = clean_nav_label(ch_title)
            if len(short_title) > 78:
                short_title = short_title[:75] + "..."
            nav_label = f"{idx}. {short_title}"
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
            safe_label = label.replace('"', "'")
            nav_lines.append(f'      - "{safe_label}": {rel_md}')

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
