#!/usr/bin/env python3
"""Generate the formatted ToyC experiment report DOCX from its Markdown source.

The implementation uses only Python's standard library and writes the minimal
Open XML parts needed by Microsoft Word/WPS.  It deliberately keeps the report
content in Markdown so later edits do not require touching XML.
"""

from __future__ import annotations

import re
import zipfile
from datetime import datetime, timezone
from pathlib import Path
from xml.etree import ElementTree as ET


ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "ToyC编译器实验报告.md"
OUTPUT = ROOT / "ToyC编译器实验报告.docx"

W = "http://schemas.openxmlformats.org/wordprocessingml/2006/main"
R = "http://schemas.openxmlformats.org/officeDocument/2006/relationships"
CP = "http://schemas.openxmlformats.org/package/2006/metadata/core-properties"
DC = "http://purl.org/dc/elements/1.1/"
DCTERMS = "http://purl.org/dc/terms/"
XSI = "http://www.w3.org/2001/XMLSchema-instance"

ET.register_namespace("w", W)
ET.register_namespace("r", R)
ET.register_namespace("cp", CP)
ET.register_namespace("dc", DC)
ET.register_namespace("dcterms", DCTERMS)
ET.register_namespace("xsi", XSI)


def qn(ns: str, tag: str) -> str:
    return f"{{{ns}}}{tag}"


def el(parent: ET.Element, tag: str, attrs: dict[str, str] | None = None,
       ns: str = W) -> ET.Element:
    node = ET.SubElement(parent, qn(ns, tag))
    if attrs:
        for key, value in attrs.items():
            node.set(qn(ns, key), value)
    return node


def set_fonts(rpr: ET.Element, ascii_font: str = "Times New Roman",
              east_asia: str = "宋体") -> None:
    el(rpr, "rFonts", {
        "ascii": ascii_font,
        "hAnsi": ascii_font,
        "eastAsia": east_asia,
        "cs": ascii_font,
    })


def add_run(paragraph: ET.Element, text: str, *, bold: bool = False,
            italic: bool = False, code: bool = False, size: int | None = None,
            east_asia: str | None = None) -> ET.Element:
    run = el(paragraph, "r")
    rpr = el(run, "rPr")
    set_fonts(rpr, "Courier New" if code else "Times New Roman",
              east_asia or ("宋体" if not code else "宋体"))
    if bold:
        el(rpr, "b")
        el(rpr, "bCs")
    if italic:
        el(rpr, "i")
        el(rpr, "iCs")
    if size is not None:
        el(rpr, "sz", {"val": str(size)})
        el(rpr, "szCs", {"val": str(size)})
    text_node = el(run, "t")
    if text.startswith(" ") or text.endswith(" ") or "  " in text:
        text_node.set("{http://www.w3.org/XML/1998/namespace}space", "preserve")
    text_node.text = text
    return run


INLINE_RE = re.compile(r"(`[^`]+`|\*\*[^*]+\*\*|(?<!\*)\*[^*]+\*(?!\*))")


def add_inline(paragraph: ET.Element, text: str, *, default_bold: bool = False,
               size: int | None = None) -> None:
    position = 0
    for match in INLINE_RE.finditer(text):
        if match.start() > position:
            add_run(paragraph, text[position:match.start()],
                    bold=default_bold, size=size)
        token = match.group(0)
        if token.startswith("`"):
            add_run(paragraph, token[1:-1], code=True, size=size or 21)
        elif token.startswith("**"):
            add_run(paragraph, token[2:-2], bold=True, size=size)
        else:
            add_run(paragraph, token[1:-1], italic=True, size=size)
        position = match.end()
    if position < len(text):
        add_run(paragraph, text[position:], bold=default_bold, size=size)


def paragraph(body: ET.Element, text: str = "", *, style: str = "Normal",
              align: str | None = None, first_line: bool | None = None,
              before: int | None = None, after: int | None = None,
              line: int | None = None, keep_next: bool = False,
              default_bold: bool = False, size: int | None = None) -> ET.Element:
    p = el(body, "p")
    ppr = el(p, "pPr")
    if style:
        el(ppr, "pStyle", {"val": style})
    if align:
        el(ppr, "jc", {"val": align})
    if first_line is not None:
        el(ppr, "ind", {"firstLine": "480" if first_line else "0"})
    spacing: dict[str, str] = {}
    if before is not None:
        spacing["before"] = str(before)
    if after is not None:
        spacing["after"] = str(after)
    if line is not None:
        spacing["line"] = str(line)
        spacing["lineRule"] = "exact"
    if spacing:
        el(ppr, "spacing", spacing)
    if keep_next:
        el(ppr, "keepNext")
    if text:
        add_inline(p, text, default_bold=default_bold, size=size)
    return p


def page_break(body: ET.Element) -> None:
    p = paragraph(body, style="Normal", first_line=False)
    run = el(p, "r")
    el(run, "br", {"type": "page"})


def code_block(body: ET.Element, lines: list[str]) -> None:
    p = paragraph(body, style="Code", first_line=False, before=80, after=120,
                  line=320)
    ppr = p.find(qn(W, "pPr"))
    assert ppr is not None
    shd = el(ppr, "shd", {"val": "clear", "color": "auto", "fill": "F3F4F6"})
    _ = shd
    el(ppr, "ind", {"left": "360", "right": "240", "firstLine": "0"})
    for index, line_text in enumerate(lines):
        run = add_run(p, line_text or " ", code=True, size=19)
        if index + 1 < len(lines):
            el(run, "br")


def clean_cell(text: str) -> str:
    text = text.strip()
    text = re.sub(r"`([^`]+)`", r"\1", text)
    text = re.sub(r"\*\*([^*]+)\*\*", r"\1", text)
    text = re.sub(r"\*([^*]+)\*", r"\1", text)
    return text


def add_table(body: ET.Element, rows: list[list[str]], *, cover: bool = False) -> None:
    if not rows:
        return
    if cover and rows and [c.strip() for c in rows[0]] == ["项目", "内容"]:
        rows = rows[1:]
    table = el(body, "tbl")
    tblpr = el(table, "tblPr")
    el(tblpr, "tblW", {"w": "0", "type": "auto"})
    el(tblpr, "jc", {"val": "center"})
    borders = el(tblpr, "tblBorders")
    border_style = "nil" if cover else "single"
    for side in ("top", "left", "bottom", "right", "insideH", "insideV"):
        attrs = {"val": border_style}
        if not cover:
            attrs.update({"sz": "6", "space": "0", "color": "808080"})
        el(borders, side, attrs)
    el(tblpr, "tblCellMar")
    for row_index, row in enumerate(rows):
        tr = el(table, "tr")
        if row_index == 0 and not cover:
            trpr = el(tr, "trPr")
            el(trpr, "tblHeader")
        for cell_index, raw in enumerate(row):
            tc = el(tr, "tc")
            tcpr = el(tc, "tcPr")
            if cover:
                width = "2200" if cell_index == 0 else "5200"
                el(tcpr, "tcW", {"w": width, "type": "dxa"})
            elif row_index == 0:
                el(tcpr, "shd", {"val": "clear", "color": "auto", "fill": "D9EAF7"})
            p = paragraph(tc, style="TableText", align="center" if row_index == 0 else "left",
                          first_line=False, before=30, after=30, line=300,
                          default_bold=(row_index == 0 or (cover and cell_index == 0)),
                          size=21 if not cover else 30)
            add_inline(p, clean_cell(raw),
                       default_bold=(row_index == 0 or (cover and cell_index == 0)),
                       size=21 if not cover else 30)
    paragraph(body, style="Normal", first_line=False, after=40)


def heading(body: ET.Element, level: int, text: str) -> None:
    paragraph(body, text, style=f"Heading{min(level, 3)}", first_line=False,
              before=240 if level == 1 else 140, after=120,
              keep_next=True)


def add_cover_heading(body: ET.Element, text: str, level: int) -> None:
    if level == 1:
        for _ in range(1 if len(body) else 3):
            paragraph(body, style="Normal", first_line=False, line=460)
        paragraph(body, text, style="CoverUniversity", align="center",
                  first_line=False, after=100, line=520)
    else:
        for _ in range(3):
            paragraph(body, style="Normal", first_line=False, line=460)
        paragraph(body, text, style="CoverExperiment", align="center",
                  first_line=False, before=180, after=260, line=640)


def parse_markdown(body: ET.Element, source: str) -> None:
    lines = source.splitlines()
    index = 0
    cover = True
    table_number = 0
    while index < len(lines):
        raw = lines[index]
        stripped = raw.strip()
        if stripped == "<!-- PAGEBREAK -->":
            page_break(body)
            cover = False
            index += 1
            continue
        if not stripped:
            index += 1
            continue
        if stripped.startswith("```"):
            code_lines: list[str] = []
            index += 1
            while index < len(lines) and not lines[index].strip().startswith("```"):
                code_lines.append(lines[index])
                index += 1
            index += 1
            code_block(body, code_lines)
            continue
        if stripped.startswith("|") and stripped.endswith("|"):
            rows: list[list[str]] = []
            while index < len(lines):
                candidate = lines[index].strip()
                if not (candidate.startswith("|") and candidate.endswith("|")):
                    break
                cells = [c.strip() for c in candidate[1:-1].split("|")]
                if not all(re.fullmatch(r":?-{3,}:?", c) for c in cells):
                    rows.append(cells)
                index += 1
            table_number += 1
            add_table(body, rows, cover=cover and table_number == 1)
            continue
        heading_match = re.match(r"^(#{1,3})\s+(.*)$", stripped)
        if heading_match:
            level = len(heading_match.group(1))
            text = heading_match.group(2)
            if cover:
                add_cover_heading(body, text, level)
            elif text == "摘要":
                paragraph(body, text, style="Heading1", align="center",
                          first_line=False, before=120, after=200, keep_next=True)
            elif text == "教师评语评分":
                paragraph(body, text, style="Heading1", align="center",
                          first_line=False, after=240, keep_next=True)
            else:
                heading(body, level, text)
            index += 1
            continue
        if re.match(r"^\*\*图\s*\d", stripped) or re.match(r"^\*\*表\s*\d", stripped):
            caption = stripped[2:-2] if stripped.endswith("**") else stripped
            paragraph(body, caption, style="Caption", align="center",
                      first_line=False, before=100, after=100,
                      default_bold=True, size=24)
            index += 1
            continue
        ordered = re.match(r"^(\d+)\.\s+(.*)$", stripped)
        bullet = re.match(r"^-\s+(.*)$", stripped)
        if ordered or bullet:
            prefix = f"{ordered.group(1)}. " if ordered else "• "
            text = ordered.group(2) if ordered else bullet.group(1)
            p = paragraph(body, style="ListText", first_line=False, before=0,
                          after=30, line=460)
            ppr = p.find(qn(W, "pPr"))
            assert ppr is not None
            el(ppr, "ind", {"left": "480", "hanging": "360"})
            add_run(p, prefix, size=24)
            add_inline(p, text, size=24)
            index += 1
            continue
        if stripped.startswith("**关键词：**"):
            paragraph(body, stripped, style="Normal", first_line=False,
                      before=120, after=120, line=460)
            index += 1
            continue
        if stripped == "**评语：**":
            paragraph(body, stripped, style="Normal", first_line=False,
                      before=120, after=80, line=460)
            for _ in range(10):
                paragraph(body, " ", style="Normal", first_line=False,
                          before=0, after=0, line=460)
            index += 1
            continue
        if cover:
            paragraph(body, stripped, style="Normal", align="center",
                      first_line=False, line=460)
        else:
            paragraph(body, stripped, style="Normal", align="both",
                      first_line=True, before=0, after=40, line=460)
        index += 1


def add_style(styles: ET.Element, style_id: str, name: str, *,
              based_on: str | None = None, size: int = 24,
              east_asia: str = "宋体", ascii_font: str = "Times New Roman",
              bold: bool = False, align: str | None = None,
              outline: int | None = None, first_line: int | None = None,
              line: int | None = None) -> None:
    style = el(styles, "style", {"type": "paragraph", "styleId": style_id})
    el(style, "name", {"val": name})
    if based_on:
        el(style, "basedOn", {"val": based_on})
    el(style, "qFormat")
    ppr = el(style, "pPr")
    if align:
        el(ppr, "jc", {"val": align})
    if outline is not None:
        el(ppr, "outlineLvl", {"val": str(outline)})
    if first_line is not None:
        el(ppr, "ind", {"firstLine": str(first_line)})
    if line is not None:
        el(ppr, "spacing", {"line": str(line), "lineRule": "exact"})
    rpr = el(style, "rPr")
    set_fonts(rpr, ascii_font, east_asia)
    if bold:
        el(rpr, "b")
        el(rpr, "bCs")
    el(rpr, "sz", {"val": str(size)})
    el(rpr, "szCs", {"val": str(size)})


def styles_xml() -> bytes:
    styles = ET.Element(qn(W, "styles"))
    defaults = el(styles, "docDefaults")
    rdefault = el(defaults, "rPrDefault")
    rpr = el(rdefault, "rPr")
    set_fonts(rpr)
    el(rpr, "sz", {"val": "24"})
    el(rpr, "szCs", {"val": "24"})
    pdefault = el(defaults, "pPrDefault")
    ppr = el(pdefault, "pPr")
    el(ppr, "spacing", {"line": "460", "lineRule": "exact", "after": "40"})

    add_style(styles, "Normal", "正文", size=24, first_line=480, line=460)
    add_style(styles, "Heading1", "一级标题", based_on="Normal", size=28,
              east_asia="黑体", bold=True, outline=0)
    add_style(styles, "Heading2", "二级标题", based_on="Normal", size=24,
              east_asia="黑体", bold=True, outline=1)
    add_style(styles, "Heading3", "三级标题", based_on="Normal", size=24,
              east_asia="黑体", bold=True, outline=2)
    add_style(styles, "CoverUniversity", "封面校名", based_on="Normal", size=52,
              east_asia="宋体", bold=True, align="center", line=560)
    add_style(styles, "CoverExperiment", "封面实验名", based_on="Normal", size=44,
              east_asia="黑体", bold=True, align="center", line=640)
    add_style(styles, "Caption", "题注", based_on="Normal", size=24,
              east_asia="黑体", bold=True, align="center")
    add_style(styles, "TableText", "表格正文", based_on="Normal", size=21,
              first_line=0, line=300)
    add_style(styles, "ListText", "列表正文", based_on="Normal", size=24,
              first_line=0, line=460)
    add_style(styles, "Code", "代码", based_on="Normal", size=19,
              east_asia="宋体", ascii_font="Courier New", first_line=0, line=320)
    return ET.tostring(styles, encoding="utf-8", xml_declaration=True)


def document_xml() -> bytes:
    document = ET.Element(qn(W, "document"))
    body = el(document, "body")
    parse_markdown(body, SOURCE.read_text(encoding="utf-8"))
    sect = el(body, "sectPr")
    el(sect, "footerReference", {"type": "default", "id": "rId1"})
    el(sect, "pgSz", {"w": "11906", "h": "16838"})
    el(sect, "pgMar", {
        "top": "1440", "right": "1701", "bottom": "1440", "left": "1701",
        "header": "720", "footer": "720", "gutter": "0",
    })
    el(sect, "docGrid", {"linePitch": "460"})
    return ET.tostring(document, encoding="utf-8", xml_declaration=True)


def footer_xml() -> bytes:
    footer = ET.Element(qn(W, "ftr"))
    p = paragraph(footer, style="Normal", align="center", first_line=False,
                  line=320)
    run = el(p, "r")
    rpr = el(run, "rPr")
    set_fonts(rpr)
    el(rpr, "sz", {"val": "18"})
    el(run, "fldChar", {"fldCharType": "begin"})
    instr = el(run, "instrText")
    instr.set("{http://www.w3.org/XML/1998/namespace}space", "preserve")
    instr.text = " PAGE "
    el(run, "fldChar", {"fldCharType": "end"})
    return ET.tostring(footer, encoding="utf-8", xml_declaration=True)


CONTENT_TYPES = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
  <Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>
  <Default Extension="xml" ContentType="application/xml"/>
  <Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"/>
  <Override PartName="/word/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.styles+xml"/>
  <Override PartName="/word/settings.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.settings+xml"/>
  <Override PartName="/word/fontTable.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.fontTable+xml"/>
  <Override PartName="/word/footer1.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.footer+xml"/>
  <Override PartName="/docProps/core.xml" ContentType="application/vnd.openxmlformats-package.core-properties+xml"/>
  <Override PartName="/docProps/app.xml" ContentType="application/vnd.openxmlformats-officedocument.extended-properties+xml"/>
</Types>
"""

PACKAGE_RELS = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
  <Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="word/document.xml"/>
  <Relationship Id="rId2" Type="http://schemas.openxmlformats.org/package/2006/relationships/metadata/core-properties" Target="docProps/core.xml"/>
  <Relationship Id="rId3" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/extended-properties" Target="docProps/app.xml"/>
</Relationships>
"""

DOCUMENT_RELS = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
  <Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/footer" Target="footer1.xml"/>
  <Relationship Id="rId2" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/>
  <Relationship Id="rId3" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/settings" Target="settings.xml"/>
  <Relationship Id="rId4" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/fontTable" Target="fontTable.xml"/>
</Relationships>
"""

SETTINGS = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<w:settings xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main">
  <w:zoom w:percent="100"/><w:defaultTabStop w:val="420"/>
  <w:characterSpacingControl w:val="doNotCompress"/>
  <w:compat><w:compatSetting w:name="compatibilityMode" w:uri="http://schemas.microsoft.com/office/word" w:val="15"/></w:compat>
</w:settings>
"""

FONT_TABLE = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<w:fonts xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main">
  <w:font w:name="宋体"/><w:font w:name="黑体"/>
  <w:font w:name="Times New Roman"/><w:font w:name="Courier New"/>
</w:fonts>
"""


def core_xml() -> bytes:
    root = ET.Element(qn(CP, "coreProperties"))
    ET.SubElement(root, qn(DC, "title")).text = "ToyC 编译器设计与优化实验报告"
    ET.SubElement(root, qn(DC, "subject")).text = "编译系统实践"
    ET.SubElement(root, qn(DC, "creator")).text = "（请填写学生姓名）"
    ET.SubElement(root, qn(CP, "keywords")).text = "ToyC; OCaml; RISC-V; 编译器优化"
    ET.SubElement(root, qn(DC, "description")).text = "武汉大学计算机学院本科生实验报告"
    created = ET.SubElement(root, qn(DCTERMS, "created"))
    created.set(qn(XSI, "type"), "dcterms:W3CDTF")
    created.text = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    return ET.tostring(root, encoding="utf-8", xml_declaration=True)


APP_XML = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?>
<Properties xmlns="http://schemas.openxmlformats.org/officeDocument/2006/extended-properties" xmlns:vt="http://schemas.openxmlformats.org/officeDocument/2006/docPropsVTypes">
  <Application>ToyC report generator</Application><AppVersion>1.0</AppVersion>
</Properties>
"""


def generate() -> None:
    parts: dict[str, bytes | str] = {
        "[Content_Types].xml": CONTENT_TYPES,
        "_rels/.rels": PACKAGE_RELS,
        "word/document.xml": document_xml(),
        "word/styles.xml": styles_xml(),
        "word/settings.xml": SETTINGS,
        "word/fontTable.xml": FONT_TABLE,
        "word/footer1.xml": footer_xml(),
        "word/_rels/document.xml.rels": DOCUMENT_RELS,
        "docProps/core.xml": core_xml(),
        "docProps/app.xml": APP_XML,
    }
    with zipfile.ZipFile(OUTPUT, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, content in parts.items():
            archive.writestr(name, content.encode("utf-8") if isinstance(content, str) else content)
    print(f"generated {OUTPUT} ({OUTPUT.stat().st_size} bytes)")


if __name__ == "__main__":
    generate()
