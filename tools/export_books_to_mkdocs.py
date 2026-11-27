#!/usr/bin/env python3
"""
SSOT Book Exporter: Compiles all 5 core books from LaTeX SSOT (`book/sources/`)
into full chapter-by-chapter MkDocs Material pages (`docs/books/<book_slug>/`).

Single Source of Truth (SSOT):
  Edit only `book/sources/**/*.tex`.
  - PDF export: `pwsh -NoProfile -File book/build.ps1 -Volume <volume>`
  - Web/MkDocs export: `python tools/export_books_to_mkdocs.py && python -m mkdocs build --strict`
"""

from __future__ import annotations

import re
import shutil
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BOOK_SOURCES = REPO_ROOT / "book" / "sources"
DOCS_BOOKS = REPO_ROOT / "docs" / "books"

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


def expand_inputs(rel_path: str) -> str:
    clean_rel = rel_path.strip()
    p = BOOK_SOURCES / clean_rel
    if not p.exists() and not clean_rel.endswith(".tex"):
        p = BOOK_SOURCES / (clean_rel + ".tex")
    if not p.exists():
        return f"% [Missing input: {clean_rel}]\n"
    text = p.read_text(encoding="utf-8")
    # Strip full-line comments
    lines = [
        line
        for line in text.splitlines()
        if not line.lstrip().startswith("%")
    ]
    joined = "\n".join(lines)
    return re.sub(r"\\input\{([^}]+)\}", lambda m: expand_inputs(m.group(1)), joined)


def unwrap_texorpdfstring(text: str) -> str:
    """Replace \\texorpdfstring{A}{B} with A (handles up to 3 levels of nested braces)."""
    brace3 = r"(?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*"
    pattern = re.compile(r"\\texorpdfstring\{(" + brace3 + r")\}\{(" + brace3 + r")\}")
    prev = None
    while prev != text:
        prev = text
        text = pattern.sub(r"\1", text)
    return text


def replace_paired_command(text: str, cmd: str, wrapper_left: str, wrapper_right: str) -> str:
    """Replace \\cmd{content} with wrapper_left + content + wrapper_right supporting nested braces."""
    pat = re.compile(r"\\" + cmd + r"\{((?:[^{}]|\{[^{}]*\})*)\}")
    prev = None
    while prev != text:
        prev = text
        text = pat.sub(lambda m: f"{wrapper_left}{m.group(1)}{wrapper_right}", text)
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
    """Convert itemize, enumerate, and description environments into Markdown lists."""
    # Remove optional enumitem args like [label=...]
    text = re.sub(r"\\begin\{(enumerate|itemize|description)\}\s*\[[^\]]*\]", r"\\begin{\1}", text)

    lines = text.splitlines()
    out_lines = []
    stack: list[str] = []
    enum_counters: list[int] = []

    for line in lines:
        stripped = line.strip()
        m_begin = re.match(r"^\\begin\{(enumerate|itemize|description)\}(.*)$", stripped)
        if m_begin:
            kind = m_begin.group(1)
            rest = m_begin.group(2).strip()
            stack.append(kind)
            enum_counters.append(0)
            if rest:
                out_lines.append(rest)
            continue

        m_end = re.match(r"^\\end\{(enumerate|itemize|description)\}(.*)$", stripped)
        if m_end:
            if stack:
                stack.pop()
                enum_counters.pop()
            rest = m_end.group(2).strip()
            if rest:
                out_lines.append(rest)
            out_lines.append("")
            continue

        if stack and stripped.startswith(r"\item"):
            indent = "  " * (len(stack) - 1)
            kind = stack[-1]
            rest = stripped[len(r"\item"):].strip()
            m_opt = re.match(r"^\[((?:[^\[\]]|\[[^\[\]]*\])*)\]\s*(.*)$", rest)
            if m_opt:
                label_txt = m_opt.group(1).strip()
                item_body = m_opt.group(2).strip()
                out_lines.append(f"{indent}- **{label_txt}** {item_body}")
            else:
                if kind == "enumerate":
                    enum_counters[-1] += 1
                    idx = enum_counters[-1]
                    out_lines.append(f"{indent}{idx}. {rest}")
                else:
                    out_lines.append(f"{indent}- {rest}")
        else:
            if stack and stripped and not stripped.startswith(("$$", "\\begin{", "\\end{")):
                indent = "  " * len(stack)
                out_lines.append(f"{indent}{stripped}")
            else:
                out_lines.append(line)

    return "\n".join(out_lines)


def convert_admonition_envs(text: str) -> str:
    """Convert theorem, definition, remark, proof, quote, center environments to MkDocs admonitions."""
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
            return f'\n\n{marker}{adm_type} "{header_title}"\n{indented}\n\n'

        text = pattern.sub(repl, text)

    return text


def latex_to_markdown(tex: str) -> str:
    text = tex

    # 1. Strip layout-only boilerplate
    text = re.sub(r"\\(?:markboth|addcontentsline)\{[^}]*\}\{[^}]*\}(?:\{[^}]*\})?", "", text)
    text = re.sub(r"\\(?:noindent|sloppy|bigskip|medskip|smallskip|allowbreak|centering)\b", "", text)
    text = re.sub(r"\\(?:vspace|setlength)\*?\{[^}]*\}(?:\{[^}]*\})?", "", text)
    text = re.sub(r"\\rule\{[^}]*\}\{[^}]*\}", "\n---\n", text)

    # 2. Expand custom macros
    text = text.replace(r"\caSignalSpeed", "c_0")
    text = text.replace(r"\speedC", "c")
    text = text.replace(r"\geomNeighborTwelve", "12")
    text = text.replace(r"\phaseRingCount", "512")
    text = text.replace(r"\latGCKshort", "ГЦК")
    text = re.sub(r"\\Axref\{ax:A([^}]+)\}", r"$A_{\1}$", text)

    # 3. Unwrap \texorpdfstring{math}{plain} -> math
    text = unwrap_texorpdfstring(text)

    # 4. Lab environments -> sections/subsections
    text = re.sub(
        r"\\begin\{labseries\}\{((?:[^{}]|\{[^{}]*\})*)\}\{([^}]*)\}",
        r"\\section{\1}",
        text,
    )
    text = re.sub(r"\\end\{labseries\}", "", text)
    text = re.sub(
        r"\\begin\{labrecord\}\{((?:[^{}]|\{[^{}]*\})*)\}\{([^}]*)\}",
        r"\\subsection{\1}",
        text,
    )
    text = re.sub(r"\\end\{labrecord\}", "", text)

    # 5. Protect display math environments (`equation`, `align`, `align*`) inside $$ ... $$
    def wrap_display_math(m: re.Match) -> str:
        env = m.group(1)
        content = m.group(2).strip()
        content = re.sub(r"\\label\{([^}]+)\}", "", content).strip()
        if env in ("align", "align*"):
            return f"\n\n$$\n\\begin{{aligned}}\n{content}\n\\end{{aligned}}\n$$\n\n"
        return f"\n\n$$\n{content}\n$$\n\n"

    text = re.sub(
        r"\\begin\{(equation\*?|align\*?)\}([\s\S]*?)\\end\{\1\}",
        wrap_display_math,
        text,
    )

    # 6. Convert tables (`\begin{table}...\end{table}` and `\begin{tabular}{...}...\end{tabular}`)
    text = re.sub(r"\\begin\{table\}(?:\[[^\]]*\])?", "", text)
    text = re.sub(r"\\end\{table\}", "", text)
    text = re.sub(r"\\resizebox\{[^}]*\}\{[^}]*\}\{", "", text)
    text = re.sub(r"\\caption\{((?:[^{}]|\{[^{}]*\})*)\}", r"\n*\1*\n", text)
    text = re.sub(
        r"\\begin\{tabular\}\{[^}]*\}([\s\S]*?)\\end\{tabular\}",
        convert_tabular,
        text,
    )

    # 7. Convert section headers
    text = re.sub(r"\\part\*?\{((?:[^{}]|\{[^{}]*\})*)\}", r"\n## Часть: \1\n", text)
    text = re.sub(r"\\section\*?\{((?:[^{}]|\{[^{}]*\})*)\}", r"\n## \1\n", text)
    text = re.sub(r"\\subsection\*?\{((?:[^{}]|\{[^{}]*\})*)\}", r"\n### \1\n", text)
    text = re.sub(r"\\subsubsection\*?\{((?:[^{}]|\{[^{}]*\})*)\}", r"\n#### \1\n", text)
    text = re.sub(r"\\paragraph\*?\{((?:[^{}]|\{[^{}]*\})*)\}", r"\n**\1**\n", text)

    # 8. Convert lists before admonitions so nested lists inside theorems/proofs indent cleanly
    text = convert_lists(text)

    # 9. Convert inline formatting (\textbf, \emph, \texttt, \url)
    text = replace_paired_command(text, "textbf", "**", "**")
    text = replace_paired_command(text, "emph", "*", "*")
    text = replace_paired_command(text, "textit", "*", "*")
    text = replace_paired_command(text, "texttt", "`", "`")
    text = replace_paired_command(text, "url", "<", ">")

    # 10. Cross-references & labels
    text = re.sub(r"\\label\{[^}]+\}", "", text)
    text = re.sub(r"\\(?:eqref|ref|cref|bcref|CiteConstruction)\{([^}]+)\}", r"`[\1]`", text)

    # 11. Convert theorem/definition/remark/proof environments to MkDocs Admonitions
    text = convert_admonition_envs(text)
    text = re.sub(r"\\begin\{(?:center|quote)\}", "\n", text)
    text = re.sub(r"\\end\{(?:center|quote)\}", "\n", text)

    # 12. Typography cleanup outside math
    text = text.replace("---", "—").replace("--", "–").replace("~", " ")
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
        raw_title = replace_paired_command(raw_title, "texttt", "`", "`")
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
            md_body = latex_to_markdown(ch_body)

            pdf_url = f"https://github.com/AI-Guiders/discrete-quantum-mechanics/raw/main/book/out/pdf/{book['pdf']}"
            ssot_url = f"https://github.com/AI-Guiders/discrete-quantum-mechanics/blob/main/book/sources/{book['entry']}"

            header_ru = (
                f"# {ch_title}\n\n"
                f"!!! abstract \"Автоматический экспорт из LaTeX SSOT (`book/sources/`)\"\n"
                f"    - **Том:** {book['title_ru']}\n"
                f"    - **PDF-версия тома:** [Скачать `{book['pdf']}`]({pdf_url})\n"
                f"    - **Исходник SSOT:** [`book/sources/{book['entry']}`]({ssot_url})\n\n"
                f"---\n\n"
            )
            header_en = (
                f"# {ch_title}\n\n"
                f"!!! abstract \"Automated Export from LaTeX SSOT (`book/sources/`)\"\n"
                f"    - **Volume:** {book['title_en']} (Full canonical text in Russian; math & Lean 4 identifiers are universal)\n"
                f"    - **PDF Volume Download:** [Download `{book['pdf']}`]({pdf_url})\n"
                f"    - **SSOT Source:** [`book/sources/{book['entry']}`]({ssot_url})\n\n"
                f"---\n\n"
            )

            (book_dir / f"{ch_file_stem}.ru.md").write_text(
                header_ru + md_body, encoding="utf-8", newline="\n"
            )
            (book_dir / f"{ch_file_stem}.md").write_text(
                header_en + md_body, encoding="utf-8", newline="\n"
            )

            short_title = clean_nav_label(ch_title)
            if len(short_title) > 78:
                short_title = short_title[:75] + "..."
            nav_label = f"{idx}. {short_title}"
            book_nav_items.append((nav_label, f"books/{slug}/{ch_file_stem}.md"))

        nav_books_en.append((book["title_en"], book["title_ru"], book_nav_items))
        nav_books_ru_translations[book["title_en"]] = book["title_ru"]

    # Update mkdocs.yml navigation deterministically
    mkdocs_yml = REPO_ROOT / "mkdocs.yml"
    yml_text = mkdocs_yml.read_text(encoding="utf-8")

    # Build nav_translations block
    trans_lines = [
        "          nav_translations:",
        "            Overview & 5 Books: Обзор и 5 книг",
        "            For Engineers, Shipbuilders & CAD: Инженерам, корабелам и САПР",
        "            For Mathematicians & Lean 4: Математикам и Lean 4",
        "            For Physicists & Natural Science: Физикам и естествоиспытателям",
    ]
    for title_en, title_ru in nav_books_ru_translations.items():
        trans_lines.append(f'            "{title_en}": "{title_ru}"')

    # Build nav block
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
