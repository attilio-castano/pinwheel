"""Draw one measured routing conflict; visualization grants no acceptance."""
import hashlib
import json
from pathlib import Path
from xml.sax.saxutils import escape

ROOT = Path(__file__).resolve().parents[1]
B = ROOT / 'build/campaigns/8x4-20261022-01'
SOURCE = B / 'route-replay-coordinate-analysis-03/report.json'
PIN = 'a73fb5aede7059b823d990d463bf95b0f2e9daaabdb0bc30a100ec4a1cdd1308'
DEST = ROOT / 'docs/physical/figures'
SCENE = B / 'diode-strap-conflict-scene-01.json'


def main():
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != PIN:
        raise ValueError('Exact independently reviewed shape analysis required')
    data = json.loads(raw)
    diode = next(r for r in data['full_A_projection_coverage'] if r['instance'] == 'ANTENNA_115')
    markers = [r for r in data['markers'] if r['sources'] == ['VPWR', 'net343']]
    if len(markers) != 2 or any(r['type'] != 'Short' for r in markers):
        raise ValueError('Exact measured example required')
    examples = [r['exact_signal_PG_shape_intersections'][0] for r in markers]
    scene = dict(source_sha256=PIN, units='integer DBU, 1000 per micrometre',
                 diode=diode, markers=markers, physical_acceptance=False,
                 scope='Illustration of measured reconstructed route only')
    stem = DEST / 'streaming-8x4-diode-strap-conflict'
    if stem.with_suffix('.svg').exists() or SCENE.exists():
        raise ValueError('Preserve existing illustration')
    parts = ['<svg xmlns="http://www.w3.org/2000/svg" width="1160" height="820" viewBox="0 0 1160 820">',
             '<rect width="1160" height="820" fill="#fbfcfe"/>',
             '<style>text{font-family:Arial,sans-serif;fill:#15243a} .small{font-size:15px} .tick{font-size:13px;fill:#526174}</style>',
             '<defs><pattern id="hatch" width="7" height="7" patternUnits="userSpaceOnUse"><path d="M0 7 L7 0" stroke="#bf173b" stroke-width="2"/></pattern></defs>']
    def text(x, y, value, size=18, extra=''):
        parts.append(f'<text x="{x}" y="{y}" font-size="{size}" {extra}>{escape(value)}</text>')
    text(40, 42, 'Measured antenna-diode access conflict', 28, 'font-weight="700"')
    text(40, 74, 'Reconstructed 8×4 route • net343 / ANTENNA_115 • actual DEF, LEF and DRC coordinates', 17)
    # Equal x/y scale; both panels show exactly the same physical window.
    xmin, xmax, ymin, ymax = 1111900, 1114500, 461900, 464600
    scale = 0.17
    for index, origin in enumerate((65, 640)):
        top, width, height = 150, (xmax-xmin)*scale, (ymax-ymin)*scale
        text(origin, 120, 'Metal1 A-pin projection' if index == 0 else 'Metal2 routed signal access', 21, 'font-weight="700"')
        parts.append(f'<rect x="{origin}" y="{top}" width="{width}" height="{height}" fill="white" stroke="#9aabc0"/>')
        def box(rect, fill, stroke, opacity=1, dash=''):
            l, d, r, u = rect
            l, r, d, u = max(l, xmin), min(r, xmax), max(d, ymin), min(u, ymax)
            if l >= r or d >= u:
                return
            x, y, w, h = origin+(l-xmin)*scale, top+(ymax-u)*scale, (r-l)*scale, (u-d)*scale
            parts.append(f'<rect x="{x:.3f}" y="{y:.3f}" width="{w:.3f}" height="{h:.3f}" fill="{fill}" stroke="{stroke}" fill-opacity="{opacity}" stroke-width="2" {dash}/>')
        strap = examples[0]['pg']['rectangle_dbu']
        box(strap, '#f8d887', '#b67d12', .45)
        if index == 0:
            for pin in diode['pin_A_rectangles_dbu']:
                box(pin, '#9f79db', '#624193', .7)
        else:
            for item in examples:
                box(item['signal']['rectangle_dbu'], '#3d9cc1', '#086484', .65)
            for marker in markers:
                box(marker['bbox_dbu'], 'url(#hatch)', '#bf173b')
        text(origin+105, top+32, 'VPWR strap, width 1.000 µm', 14)
        for value in (1112000, 1113000, 1114000):
            x = origin+(value-xmin)*scale
            text(x-28, top+height+24, f'{value/1000:.0f}', 13)
        text(origin+150, top+height+48, 'x position (µm)', 14)
        for value in (462000, 463000, 464000):
            y = top+(ymax-value)*scale
            text(origin-43, y+4, f'{value/1000:.0f}', 13)
        if index == 0:
            text(origin, 688, 'All three A-pin rectangles lie beneath the strap.', 16)
            text(origin, 713, 'Cross-layer projection alone is not a short.', 16)
        else:
            text(origin, 688, 'Red hatching: two exact same-layer Short markers.', 16)
            text(origin, 713, 'Via1 enclosure and default-width wire overlap VPWR.', 16)
    text(40, 767, 'Diagnostic reconstruction: fresh readDesign differs from the historical in-memory reroute.', 15)
    text(40, 793, 'Source: independently reviewed analysis03 a73fb5ae… • Not a final routed or signoff-accepted layout.', 15)
    parts.append('</svg>')
    stem.with_suffix('.svg').write_text('\n'.join(parts)+'\n')
    SCENE.write_text(json.dumps(scene, indent=2)+'\n')
    print(stem.with_suffix('.svg'))


if __name__ == '__main__':
    main()
