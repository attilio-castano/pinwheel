"""Generate narrowly patched pinned sources without modifying their originals."""
import difflib
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(sys.argv[1]).resolve()
SOURCE = ROOT / "source"
OUTPUT = ROOT / (sys.argv[2] if len(sys.argv) > 2 else "generated")
if OUTPUT.exists():
    assert not any(OUTPUT.iterdir()), "Refuse to replace prepared artifacts"
else:
    OUTPUT.mkdir()

def replace(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new)

def function(text, signature):
    start = text.index(signature)
    begin = text.index("{", start)
    depth = 1
    position = begin + 1
    while depth:
        depth += (text[position] == "{") - (text[position] == "}")
        position += 1
    return text[start:position]

original = (SOURCE / "src/drt/src/io/io.cpp").read_text()
body = function(original, "void io::Parser::updateNetRouting(")
regular, special = body.split("  if (net->isSpecial()) {", 1)
patched = replace(regular, "  odb::dbWireDecoder decoder;", """  // Serialized default/TAPER state is per path, never inherited across a new path.
  odb::dbTechNonDefaultRule* path_ndr = nullptr;
  odb::dbWireDecoder decoder;""")
patched = replace(patched, "          case odb::dbWireDecoder::VWIRE:\n            prevLayer", "          case odb::dbWireDecoder::VWIRE:\n            path_ndr = nullptr;\n            prevLayer")
patched = replace(patched, "          case odb::dbWireDecoder::ITERM:\n          case odb::dbWireDecoder::BTERM:\n          case odb::dbWireDecoder::RULE:", """          case odb::dbWireDecoder::RULE:
            if (decoder.getRule() == nullptr) {
              throw std::runtime_error("Pinwheel importer: null per-path layer rule on net " + net->getName());
            }
            path_ndr = decoder.getRule()->getNonDefaultRule();
            if (path_ndr == nullptr || path_ndr != net->getNonDefaultRule()) {
              throw std::runtime_error("Pinwheel importer: distinct per-path TAPERRULE is unsupported on net " + net->getName());
            }
            break;
          case odb::dbWireDecoder::ITERM:
          case odb::dbWireDecoder::BTERM:""")
patched = replace(patched, "      if (hasRect) {", """      if (hasRect && path_ndr != nullptr) {
        throw std::runtime_error("Pinwheel importer: NDR RECT cannot be represented faithfully on net " + net->getName());
      }
      if (hasRect) {""")
patched = replace(patched, "        auto styleWidth = width;", """        auto styleWidth = width;
        if (path_ndr != nullptr) {
          auto db_layer = net->getBlock()->getTech()->findLayer(layerName.c_str());
          auto layer_rule = path_ndr->getLayerRule(db_layer);
          if (layer_rule == nullptr || layer_rule->getWidth() <= 0) {
            throw std::runtime_error("Pinwheel importer: missing/invalid NDR layer width on net " + net->getName());
          }
          styleWidth = layer_rule->getWidth();
        }""")
patched = replace(patched, "        width = getTech()->name2layer_[layerName]->getWidth();", "        width = styleWidth;")
patched = replace(patched, "        tmpP->setStyle(tmpSegStyle);", """        tmpP->setStyle(tmpSegStyle);
        tmpP->setTapered(net->getNonDefaultRule() != nullptr && path_ndr == nullptr);""")
patched = replace(patched, "          tmpP->addToNet(netIn);", """          tmpP->setTapered(net->getNonDefaultRule() != nullptr && path_ndr == nullptr);
          tmpP->addToNet(netIn);""")
complete = replace(original, body, patched + "  if (net->isSpecial()) {" + special)
complete = replace(complete, "#include <sstream>", "#include <sstream>\n#include <stdexcept>")
(OUTPUT / "io-patched.cpp").write_text(complete)
(OUTPUT / "import-preservation.patch").write_text("".join(difflib.unified_diff(original.splitlines(True), complete.splitlines(True), fromfile="pinned/io.cpp", tofile="preserved/io.cpp")))

entry = (SOURCE / "src/drt/src/TritonRoute.cpp").read_text()
prefix = entry[:entry.index("namespace drt {")] + "\n#include <stdexcept>\n"
init = function(entry, "void TritonRoute::initDesign()")
main = function(entry, "int TritonRoute::main()")
main_audit = replace(main, "  initDesign();", "  initDesign();\n  pinwheel_audit_import(db_, getDesign());")
main_audit = replace(main_audit, "  if (!initGuide()) {\n    gr();", "  if (!initGuide()) {\n    throw std::runtime_error(\"Pinwheel preservation: source guides rejected; global-routing fallback is forbidden\");\n    gr();")
(OUTPUT / "entrypoints.cpp").write_text(prefix + "\nnamespace drt {\nvoid pinwheel_audit_import(odb::dbDatabase*, frDesign*);\n" + init + "\n" + main_audit + "\n}\n")
header = SOURCE / "src/drt/include/drt/TritonRoute.h"
copied = replace(header.read_text(), "class TritonRoute\n{", "class TritonRoute\n{\n  friend class PinwheelDRTPreservation;")
(OUTPUT / "include/drt").mkdir(parents=True)
(OUTPUT / "include/drt/TritonRoute.h").write_text(copied)
paths = [SOURCE / "src/drt/src/io/io.cpp", SOURCE / "src/drt/src/TritonRoute.cpp", header]
(ROOT / "source-preparation.json").write_text(json.dumps({
    "status": "prepared", "revision": "dcf36133a369abc8f3c5e5738cd4d82e4903c0e0",
    "original_sources_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
    "copied_native_entrypoints_unchanged_except_one_preGC_read_only_audit": True,
    "native_main_requires_normal_full_scheduler": True,
    "generated_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in OUTPUT.rglob("*") if p.is_file()}}, indent=2) + "\n")
print("Prepared pinned importer repair and ordinary native entry points.")
