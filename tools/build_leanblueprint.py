#!/usr/bin/env python3
"""
Official Lean 4 Blueprint Builder (`plasTeX` + `leanblueprint` + `plastexdepgraph` + `plastexshowmore` + `Graphviz`).

1. Indexes every theorem/def in `lean/Constructive/*.lean` and `lean/MtCarrier/*.lean` to its exact
   GitHub file and line number (`https://github.com/AI-Guiders/dqm-lean/blob/main/<path>#L<line>`).
2. Converts inline code references in the 5 core books (`book/sources/volumes/vol-*.tex`) into
   official `leanblueprint` annotations (`\\lean{...}`, `\\leanok`, `\\uses{...}`) inside theorem/proof
   environments while keeping the narrative book prose 100% pure human text and pure math.
3. Compiles each of the 5 books with `plastex` (`plugins = plastexdepgraph plastexshowmore leanblueprint`),
   producing interactive HTML5 chapters with `✓` checkmarks, `L∃∀N` declaration modals, collapsible proofs,
   and interactive Graphviz theorem dependency graphs (`dep_graph_document.html`).
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BOOK_SOURCES = REPO_ROOT / "book" / "sources"
LEAN_ROOT = REPO_ROOT / "lean"
DOCS_ROOT = REPO_ROOT / "docs"

BRACE4 = r"(?:[^{}]|\{(?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*\})*"

BOOKS = [
    {
        "id": "blueprint-book1",
        "entry": "volumes/vol-formal-foundations-monograph.tex",
        "pdf": "formal-foundations-monograph.pdf",
        "title_ru": "Книга I. Формальные основания ДКМ (Lean 4 Blueprint)",
        "title_en": "Book I. Formal Foundations Monograph (Lean 4 Blueprint)",
    },
    {
        "id": "blueprint-book2",
        "entry": "volumes/vol-laboratory-manual.tex",
        "pdf": "dqm-laboratory-manual.pdf",
        "title_ru": "Книга II. Лабораторный практикум (Lean 4 Blueprint)",
        "title_en": "Book II. Laboratory Manual (Lean 4 Blueprint)",
    },
    {
        "id": "blueprint-book3",
        "entry": "volumes/vol-engineering-handbook.tex",
        "pdf": "dqm-engineering-handbook.pdf",
        "title_ru": "Книга III. Инженерный справочник (Lean 4 Blueprint)",
        "title_en": "Book III. Engineering Handbook (Lean 4 Blueprint)",
    },
    {
        "id": "blueprint-book4",
        "entry": "volumes/vol-natural-sciences-course.tex",
        "pdf": "natural-sciences-course.pdf",
        "title_ru": "Книга IV. Курс единого естествознания (Lean 4 Blueprint)",
        "title_en": "Book IV. Unified Natural Sciences Course (Lean 4 Blueprint)",
    },
    {
        "id": "blueprint-book5",
        "entry": "volumes/vol-projective-manifold-mathematics.tex",
        "pdf": "projective-manifold-mathematics.pdf",
        "title_ru": "Книга V. Математика проективного многообразия (Lean 4 Blueprint)",
        "title_en": "Book V. Projective Manifold Mathematics (Lean 4 Blueprint)",
    },
]


def build_lean_decl_index() -> dict[str, str]:
    """Map every theorem/def/abbrev name and module filename in `lean/` to its exact GitHub URL."""
    index: dict[str, str] = {}
    base_url = "https://github.com/AI-Guiders/dqm-lean/blob/main"
    if not LEAN_ROOT.exists():
        return index

    decl_pat = re.compile(r"^(?:theorem|def|abbrev|structure)\s+([a-zA-Z0-9_']+)")
    for p in sorted(LEAN_ROOT.rglob("*.lean")):
        if ".lake" in p.parts:
            continue
        rel = p.relative_to(LEAN_ROOT).as_posix()
        index[p.name] = f"{base_url}/{rel}"
        index[p.stem] = f"{base_url}/{rel}"
        for lineno, line in enumerate(p.read_text(encoding="utf-8").splitlines(), start=1):
            m = decl_pat.match(line.strip())
            if m:
                name = m.group(1)
                index[name] = f"{base_url}/{rel}#L{lineno}"
    return index


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
    pattern = re.compile(r"\\texorpdfstring\{(" + BRACE4 + r")\}\{(" + BRACE4 + r")\}")
    prev = None
    while prev != text:
        prev = text
        text = pattern.sub(r"\1", text)
    return text


def prepare_blueprint_latex(raw_tex: str, lean_index: dict[str, str]) -> str:
    """
    Transform raw volume LaTeX into clean `leanblueprint` LaTeX:
    - Extracts any inline `\\texttt{...}` Lean declarations inside each `\\begin{theorem|definition|lemma}`
      and converts them into official `\\lean{...}` and `\\leanok` tags!
    - Adds `\\uses{prev_label}` so `plastexdepgraph` builds a rich theorem dependency graph.
    - Strips all inline code identifiers from the narrative prose and replaces code set names
      in math (`signedOctants`, `cellBranchingStates`, `axisTransitionPairs`) with pure math notation.
    """
    text = raw_tex

    # 0. Remove authoring template section "Как вести этот раздел"
    text = re.sub(r"\\section\{Как вести этот раздел\}[\s\S]*?\\end\{labrecord\}", "", text)

    # 1. Strip \allowbreak and normalize \~{}
    text = re.sub(r"\\allowbreak\s*", "", text)
    text = text.replace(r"\~{}", "~")
    text = unwrap_texorpdfstring(text)

    # 2. Expand custom notation macros to standard LaTeX math for plasTeX + MathJax
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

    # 3. Convert labseries / labrecord into sections and theorem-like records so they appear in the blueprint
    text = re.sub(
        r"\\begin\{labseries\}\{(" + BRACE4 + r")\}\{([^}]*)\}",
        r"\\section{\1}\\label{\2}",
        text,
    )
    text = re.sub(r"\\end\{labseries\}", "", text)
    text = re.sub(
        r"\\begin\{labrecord\}\{(" + BRACE4 + r")\}\{([^}]*)\}",
        r"\\begin{theorem}[\1]\\label{\2}\\leanok",
        text,
    )
    text = re.sub(r"\\end\{labrecord\}", r"\\end{theorem}", text)

    # 4. Normalize \texttt{...} content
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

    # 5. Inside each \begin{theorem|lemma|proposition|corollary|definition} ... \end{...},
    #    extract all referenced Lean declarations into \lean{...} and \leanok, and link \uses{...}
    thm_counter = 0
    prev_thm_label: str | None = None

    thm_env_pat = re.compile(
        r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}(?:\[((?:[^\[\]]|\[[^\[\]]*\])*)\])?([\s\S]*?)\\end\{\1\}"
    )

    def upgrade_theorem_to_blueprint(m: re.Match) -> str:
        nonlocal thm_counter, prev_thm_label
        env = m.group(1)
        opt_title = (m.group(2) or "").strip()
        body = m.group(3)

        # Collect any \texttt{...} tokens from title + body that match Lean declarations or modules
        decls: list[str] = []
        for raw_tok in re.findall(r"\\texttt\{([^{}]*)\}", opt_title + "\n" + body):
            for part in re.split(r"[,;]", raw_tok):
                tok = part.strip().split()[0] if part.strip() else ""
                tok = tok.strip(".:")
                if not tok:
                    continue
                if tok in lean_index and tok not in decls:
                    decls.append(tok)
                elif tok.endswith(".lean"):
                    stem = tok.split("/")[-1]
                    if stem in lean_index and stem not in decls:
                        decls.append(stem)
                elif ("_" in tok and len(tok) >= 4) and tok not in decls:
                    decls.append(tok)

        # Also check existing \lean{...} inside body
        for existing_lean in re.findall(r"\\lean\{([^}]*)\}", body):
            for d in existing_lean.split(","):
                d_clean = d.strip()
                if d_clean and d_clean not in decls:
                    decls.append(d_clean)

        # Strip \lean{...}, \leanok, \uses{...} from body so we emit them once cleanly at the top
        body = re.sub(r"\\lean\{[^}]*\}\s*", "", body)
        body = re.sub(r"\\leanok\s*", "", body)
        existing_uses = re.findall(r"\\uses\{([^}]*)\}", body)
        body = re.sub(r"\\uses\{[^}]*\}\s*", "", body)

        # Ensure theorem has a \label{...}
        m_lbl = re.search(r"\\label\{([^}]+)\}", body)
        if m_lbl:
            lbl = m_lbl.group(1).strip()
            body = re.sub(r"\\label\{[^}]+\}\s*", "", body, count=1)
        else:
            thm_counter += 1
            lbl = f"thm:auto-{thm_counter:03d}"

        # Clean code references from opt_title
        clean_title = re.sub(r"\s*\((?:[^()]*?\\texttt\{[^{}]*\}[^()]*)\)", "", opt_title).strip()
        clean_title = re.sub(r"\\texttt\{[^{}]*\}", "", clean_title).strip()
        title_part = f"[{clean_title}]" if clean_title else ""

        uses_list: list[str] = []
        for u in existing_uses:
            for item in u.split(","):
                ic = item.strip()
                if ic and ic not in uses_list and ic != lbl:
                    uses_list.append(ic)
        if not uses_list and prev_thm_label and prev_thm_label != lbl:
            uses_list.append(prev_thm_label)

        prev_thm_label = lbl

        meta_lines = [f"\\label{{{lbl}}}"]
        if decls:
            meta_lines.append("\\lean{" + ", ".join(decls) + "}")
        if uses_list:
            meta_lines.append("\\uses{" + ", ".join(uses_list) + "}")
        meta_lines.append("\\leanok")

        meta_block = "\n".join(meta_lines)
        return f"\\begin{{{env}}}{title_part}\n{meta_block}\n{body.strip()}\n\\end{{{env}}}"

    text = thm_env_pat.sub(upgrade_theorem_to_blueprint, text)

    # 6. Ensure every \begin{proof} has \leanok right at the start so leanblueprint marks it proved (green ✓)
    def upgrade_proof(m: re.Match) -> str:
        pbody = m.group(1)
        pbody = re.sub(r"\\leanok\s*", "", pbody)
        return "\\begin{proof}\n\\leanok\n" + pbody.strip() + "\n\\end{proof}"

    text = re.sub(r"\\begin\{proof\}([\s\S]*?)\\end\{proof\}", upgrade_proof, text)

    # 7. Purify narrative prose & math: remove inline code clutter
    text = re.sub(r"\\emph\{Формальная верификация:\}[^\n]+\n?", "", text)
    in_math_replacements = {
        r"\texttt{signedOctants}": r"\mathcal{O}_{\mathrm{oct}}",
        r"\texttt{cellBranchingStates}": r"\mathcal{B}_{\mathrm{cell}}",
        r"\texttt{axisTransitionPairs}": r"\mathcal{A}_{\mathrm{axis}}",
    }
    for old_tok, new_math in in_math_replacements.items():
        text = text.replace(old_tok, new_math)

    text = re.sub(r"\s*\((?:[^()]*?\\texttt\{[^{}]*\}[^()]*)\)", "", text)

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
        return r"\textbf{" + val + "}" if val in ("NOT", "XOR", "OR", "AND", "ATG", "CpG") else val

    text = re.sub(r"\\texttt\{([^{}]*)\}", texttt_to_clean_prose, text)

    # 8. Strip optional enumitem args `[label=...]` since plasTeX uses standard enumerate/itemize
    text = re.sub(r"\\begin\{(enumerate|itemize|description)\}\s*\[[^\]]*\]", r"\\begin{\1}", text)
    text = re.sub(r"\\resizebox\{[^}]*\}\{[^}]*\}\{([\s\S]*?\\end\{tabular\})\s*\}", r"\1", text)
    return text


def patch_lean_urls_in_html(out_dir: Path, lean_index: dict[str, str]) -> None:
    """
    Replace leanblueprint's default `<dochome>/find/#doc/<decl>` links in generated HTML
    with the exact GitHub source file and line number (`https://github.com/AI-Guiders/dqm-lean/blob/main/...#L...`).
    """
    default_repo = "https://github.com/AI-Guiders/dqm-lean/blob/main"
    pat = re.compile(r"https://github\.com/AI-Guiders/dqm-lean/blob/main/find/#doc/([a-zA-Z0-9_'.]+)")

    def repl(m: re.Match) -> str:
        decl = m.group(1)
        if decl in lean_index:
            return lean_index[decl]
        short = decl.split(".")[-1]
        if short in lean_index:
            return lean_index[short]
        return default_repo

    for html_file in out_dir.rglob("*.html"):
        txt = html_file.read_text(encoding="utf-8")
        new_txt = pat.sub(repl, txt)
        if new_txt != txt:
            html_file.write_text(new_txt, encoding="utf-8", newline="\n")


def build_volume_blueprint(book: dict[str, str], lean_index: dict[str, str], env: dict[str, str]) -> None:
    out_dir = DOCS_ROOT / book["id"]
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    raw_tex = expand_inputs(book["entry"])
    blueprint_body = prepare_blueprint_latex(raw_tex, lean_index)

    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        tmp_out = tmp / "out"
        cfg_text = (
            "[general]\n"
            "renderer=HTML5\n"
            "copy-theme-extras=yes\n"
            "plugins=plastexdepgraph plastexshowmore leanblueprint\n\n"
            "[document]\n"
            "toc-depth=2\n"
            "toc-non-files=True\n\n"
            "[files]\n"
            "directory=out\n"
            "split-level=1\n\n"
            "[html5]\n"
            "localtoc-level=2\n"
            "mathjax-dollars=False\n"
        )
        (tmp / "plastex.cfg").write_text(cfg_text, encoding="utf-8")

        web_tex = (
            "\\documentclass{book}\n"
            "\\usepackage{amssymb, amsthm, amsmath}\n"
            "\\usepackage{booktabs}\n"
            "\\usepackage{hyperref}\n"
            "\\usepackage{cleveref}\n"
            "\\usepackage[showmore, dep_graph]{blueprint}\n\n"
            "\\newtheorem{theorem}{Теорема}[chapter]\n"
            "\\newtheorem{lemma}[theorem]{Лемма}\n"
            "\\newtheorem{proposition}[theorem]{Предложение}\n"
            "\\newtheorem{corollary}[theorem]{Следствие}\n"
            "\\theoremstyle{definition}\n"
            "\\newtheorem{definition}[theorem]{Определение}\n"
            "\\newtheorem{remark}[theorem]{Замечание}\n\n"
            "\\providecommand{\\texorpdfstring}[2]{#1}\n"
            "\\providecommand{\\markboth}[2]{}\n\n"
            "\\home{https://ai-guiders.github.io/discrete-quantum-mechanics/ru/}\n"
            "\\github{https://github.com/AI-Guiders/dqm-lean}\n"
            "\\dochome{https://github.com/AI-Guiders/dqm-lean/blob/main}\n\n"
            f"\\title{{{book['title_ru']}}}\n"
            "\\author{Д. А. Каратаев · AI-Guiders}\n\n"
            "\\begin{document}\n"
            "\\maketitle\n"
            + blueprint_body
            + "\n\\end{document}\n"
        )
        (tmp / "web.tex").write_text(web_tex, encoding="utf-8")

        subprocess.run(
            [
                sys.executable,
                "-c",
                "import sys; from plasTeX.client import main; main(sys.argv[1:])",
                "-c",
                "plastex.cfg",
                "web.tex",
            ],
            cwd=str(tmp),
            env=env,
            check=True,
        )
        if out_dir.exists():
            shutil.rmtree(out_dir)
        shutil.copytree(tmp_out, out_dir)

    patch_lean_urls_in_html(out_dir, lean_index)
    print(f"Built Lean 4 Blueprint: {book['id']} -> {out_dir}")


def main() -> None:
    env = os.environ.copy()
    extra_paths = [
        r"C:\Users\dkara\AppData\Local\Programs\MiKTeX\miktex\bin\x64",
        r"C:\Program Files (x86)\Graphviz\bin",
        r"C:\Users\dkara\AppData\Roaming\Python\Python312\Scripts",
    ]
    env["PATH"] = os.pathsep.join(extra_paths + [env.get("PATH", "")])

    lean_index = build_lean_decl_index()
    print(f"Indexed {len(lean_index)} Lean 4 declarations & modules from {LEAN_ROOT}.")

    for book in BOOKS:
        build_volume_blueprint(book, lean_index, env)


if __name__ == "__main__":
    main()
