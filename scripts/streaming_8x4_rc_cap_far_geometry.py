"""HOST geometry and strict actual DEF/NDR census for the four-case far-row study.

Only straight M1 wires are admitted. No via normalization or general DEF
equivalence is provided. Native before/after bytes must remain identical.
"""
import re

import streaming_8x4_rc_consumer_cap as C

need = C.need
CASES = [('self16', 'TYP-w.16-self', '.16', None, 'training'),
         ('pair18', 'TYP-w.16-s.18', '.16', '.18', 'known_development'),
         ('pair36', 'TYP-w.16-s.36', '.16', '.36', 'held_out_consumer'),
         ('self32', 'TYP-w.32-self', '.32', None, 'wider_stress')]
JOBS = ['retained-isolation512', 'retained-isolation1024', 'far-isolation512', 'far-isolation1024']
NDR = {'Metal1': {'width_dbu': 320, 'spacing_dbu': 210},
       'Metal2': {'width_dbu': 200, 'spacing_dbu': 0}, 'Metal3': {'width_dbu': 200, 'spacing_dbu': 0},
       'Metal4': {'width_dbu': 200, 'spacing_dbu': 0}, 'TopMetal1': {'width_dbu': 1640, 'spacing_dbu': 0}}


def definition(job):
    need(job in JOBS, 'Undeclared far-row job')
    policy, sep = job.split('-isolation'); sep = int(sep); padding = 32 if sep == 512 else 64
    rows = []; partners = {}
    for ci, (name, case, width, spacing, role) in enumerate(CASES):
        width_dbu = int(C.D(width) * 1000)
        for li, length in enumerate((50, 100, 150)):
            center = (padding + (ci * 3 + li) * sep) * 1000
            offsets = [0] if spacing is None else [-int((C.D(spacing) + C.D(width)) * 500), int((C.D(spacing) + C.D(width)) * 500)]
            nets = []
            for wi, offset in enumerate(offsets):
                net = name + '_L' + str(length) + '_W' + str(wi + 1); nets.append(net)
                rows.append(dict(net=net, case=case, role=role, length_um=length, conductor='W' + str(wi + 1),
                    width_DBU=width_dbu, NDR='WIDE_Metal1' if width_dbu == 320 else None,
                    start_DBU=[padding * 1000, center + offset], end_DBU=[(padding + length) * 1000, center + offset]))
            for net in nets: partners[net] = None if len(nets) == 1 else next(n for n in nets if n != net)
    return dict(job=job, policy=policy, separation_um=sep, padding_um=padding, rows=rows, partners=partners,
                diearea_DBU=[0,0,(150+2*padding)*1000,(11*sep+2*padding)*1000])


def ndr_block():
    lines = ['NONDEFAULTRULES 1 ;', '- WIDE_Metal1']
    for metal, row in NDR.items():
        line = '  + LAYER ' + metal + ' WIDTH ' + str(row['width_dbu'])
        if row['spacing_dbu']: line += ' SPACING ' + str(row['spacing_dbu'])
        lines.append(line)
    return '\n'.join(lines + [' ;', 'END NONDEFAULTRULES']) + '\n'


def physical_join(cases):
    """Bind each emitted wire's width/gap to the exact existing FVM rectangle."""
    need([c['name'] for c in cases] == [r[1] for r in CASES], 'Far-row physical case universe differs')
    result = []
    for case, (prefix, name, width, spacing, _) in zip(cases, CASES):
        w = C.D(width)
        centers = [C.D(0)] if spacing is None else [-(C.D(spacing)+w)/2, (C.D(spacing)+w)/2]
        expected = [[center-w/2, center+w/2, C.D('1.04'), C.D('1.46')] for center in centers]
        need([r['name'] for r in case['rectangles']] == ['W'+str(i+1) for i in range(len(centers))]
             and [[C.D(x) for x in r['bounds_um']] for r in case['rectangles']] == expected,
             'Far-row reference-to-DEF drawn width/gap/height differs')
        need(case['epsilon_layers'] == cases[0]['epsilon_layers'], 'Far-row TYP material stack differs')
        for job in JOBS:
            d = definition(job)
            for row in (r for r in d['rows'] if r['case'] == name):
                ci = [r[0] for r in CASES].index(prefix)
                li = (50,100,150).index(row['length_um'])
                center = C.D((d['padding_um'] + (ci*3+li)*d['separation_um'])*1000)
                physical_center = (C.D(row['start_DBU'][1])-center)/1000
                index = int(row['conductor'][1:])-1
                need(physical_center == centers[index] and C.D(row['width_DBU'])/1000 == w
                     and row['end_DBU'][0]-row['start_DBU'][0] == row['length_um']*1000,
                     'Far-row emitted DBU-to-physical reference witness differs')
        result.append(dict(case=name, rectangles_um=[[str(x) for x in row] for row in expected]))
    return dict(cases=result, full_Typical_epsilon_layers=cases[0]['epsilon_layers'],
        reference_transverse_x_equals_DEF_y_relative_to_group_center=True,
        reference_extrusion_equals_DEF_x=True, DBU_per_um=1000)


def fixture(job):
    pins = []; nets = []
    for row in job['rows']:
        net = row['net']; half = row['width_DBU'] // 2
        for suffix, point, direction in (('A', row['start_DBU'], 'INPUT'), ('B', row['end_DBU'], 'OUTPUT')):
            pins.append(f'- {net}_{suffix} + NET {net} + DIRECTION {direction} + USE SIGNAL\n'
                        f' + PORT + LAYER Metal1 ( -{half} -{half} ) ( {half} {half} ) + FIXED ( {point[0]} {point[1]} ) N ;')
        a, b = row['start_DBU'], row['end_DBU']; ndr = ' + NONDEFAULTRULE WIDE_Metal1' if row['NDR'] else ''
        nets.append(f'- {net} ( PIN {net}_A ) ( PIN {net}_B ){ndr}\n'
                    f' + ROUTED Metal1 ( {a[0]} {a[1]} ) ( {b[0]} {b[1]} ) ;')
    _, _, xmax, ymax = job['diearea_DBU']
    return ('VERSION 5.8 ;\nDIVIDERCHAR "/" ;\nBUSBITCHARS "[]" ;\nDESIGN rc_far_probe ;\n'
        'UNITS DISTANCE MICRONS 1000 ;\n' + f'DIEAREA ( 0 0 ) ( {xmax} {ymax} ) ;\n' + ndr_block()
        + 'COMPONENTS 0 ;\nEND COMPONENTS\n' + f'PINS {len(pins)} ;\n' + '\n'.join(pins)
        + '\nEND PINS\n' + f'NETS {len(nets)} ;\n' + '\n'.join(nets) + '\nEND NETS\nEND DESIGN\n')


def native_ndr(text):
    block = re.findall(r'^\s*NONDEFAULTRULES\s+(\d+)\s*;\s*(.*?)^\s*END\s+NONDEFAULTRULES\s*$', text, re.M | re.S)
    need(len(block) == 1 and block[0][0] == '1', 'Exactly one block-local far-row NDR required')
    rules = re.findall(r'^\s*-\s+(\S+)\s+(.*?)\s*;', block[0][1], re.M | re.S)
    need(len(rules) == 1 and rules[0][0] == 'WIDE_Metal1'
         and not re.sub(r'^\s*-\s+(\S+)\s+(.*?)\s*;', '', block[0][1], flags=re.M | re.S).strip(),
         'Unknown/duplicate far-row NDR')
    tokens = rules[0][1].split(); found = {}; i = 0
    while i < len(tokens):
        need(tokens[i:i+2] == ['+', 'LAYER'] and i + 5 <= len(tokens), 'Unsupported NDR attributes')
        layer = tokens[i+2]
        need(layer not in found and tokens[i+3] == 'WIDTH' and tokens[i+4].isdigit(), 'Invalid NDR layer/width')
        width = int(tokens[i+4]); spacing = 0; i += 5
        if i < len(tokens) and tokens[i] == 'SPACING':
            need(i + 1 < len(tokens) and tokens[i+1].isdigit(), 'Invalid NDR spacing'); spacing = int(tokens[i+1]); i += 2
        found[layer] = dict(width_dbu=width, spacing_dbu=spacing)
    need(found == NDR, 'Actual NDR layer widths/spacings differ')
    return found


def validate(text, job):
    need(re.findall(r'^\s*UNITS DISTANCE MICRONS\s+(\d+)\s*;', text, re.M) == ['1000']
         and re.findall(r'^\s*COMPONENTS\s+(\d+)\s*;', text, re.M) == ['0'], 'Actual far-row DEF DBU/cell inventory differs')
    die=re.findall(r'\bDIEAREA\s+\(\s*(-?\d+)\s+(-?\d+)\s*\)\s+\(\s*(-?\d+)\s+(-?\d+)\s*\)\s*;',text)
    need(len(die)==1 and list(map(int,die[0]))==job['diearea_DBU'],'Actual far-row outline differs')
    ndr = native_ndr(text); wanted = {r['net']: r for r in job['rows']}
    blocks = re.findall(r'^\s*NETS\s+(\d+)\s*;(.*?)^\s*END NETS\s*$', text, re.M | re.S)
    need(len(blocks) == 1 and blocks[0][0] == '18', 'Actual complete eighteen-net census differs')
    entries = list(re.finditer(r'^\s*-\s+(\w+)\s+(.*?)\s*;', blocks[0][1], re.M | re.S))
    need(len(entries) == 18 and not re.sub(r'^\s*-\s+(\w+)\s+(.*?)\s*;', '', blocks[0][1], flags=re.M | re.S).strip(),
         'Missing/extra far-row net syntax')
    actual = {}
    for entry in entries:
        name, body = entry.groups(); need(name in wanted and name not in actual, 'Duplicate/foreign far-row net')
        row = wanted[name]; refs = re.findall(r'\+\s+NONDEFAULTRULE\s+(\S+)', body)
        need(refs == ([row['NDR']] if row['NDR'] else []), 'Actual NDR binding differs')
        ports = re.findall(r'\(\s*PIN\s+(\w+)\s*\)', body)
        need(len(ports) == 2 and set(ports) == {name+'_A',name+'_B'}, 'Actual net-to-port binding differs')
        paths = re.split(r'\+\s+ROUTED\s+', body)
        need(len(paths) == 2 and re.fullmatch(r'Metal1\s+(?:\(\s*(?:-?\d+|\*)\s+(?:-?\d+|\*)\s*\)\s*){2}', paths[1].strip()),
             'Unsupported far-row routed via/metal/point')
        prefix = re.sub(r'\(\s*PIN\s+\w+\s*\)', '', paths[0])
        prefix = re.sub(r'\+\s+NONDEFAULTRULE\s+\S+', '', prefix)
        need(len(re.findall(r'\+\s+USE\b', prefix)) <= 1, 'Duplicate far-row net use attribute')
        prefix = re.sub(r'\+\s+USE\s+SIGNAL\b', '', prefix)
        need(not prefix.strip(), 'Unsupported far-row net attributes')
        points = re.findall(r'\(\s*(-?\d+|\*)\s+(-?\d+|\*)\s*\)', paths[1]); decoded = []
        for point in points:
            need(decoded or '*' not in point, 'Unbound actual DEF wildcard')
            decoded.append([decoded[-1][i] if v == '*' else int(v) for i,v in enumerate(point)])
        width = ndr['Metal1']['width_dbu'] if refs else 160
        need(decoded == [row['start_DBU'],row['end_DBU']] and width == row['width_DBU'], 'Actual wire dimensions/effective width differ')
        actual[name] = dict(points_DBU=decoded, width_DBU=width, NDR=row['NDR'])
    pins = re.findall(r'^\s*PINS\s+(\d+)\s*;(.*?)^\s*END PINS\s*$', text, re.M | re.S)
    need(len(pins) == 1 and pins[0][0] == '36', 'Actual complete thirty-six-port census differs')
    pattern = re.compile(r'\s*-\s+(\w+)\s+\+ NET\s+(\w+)\s+\+ DIRECTION\s+(INPUT|OUTPUT)\s+\+ USE SIGNAL\s+\+ PORT\s+\+ LAYER Metal1\s+\(\s*(-?\d+)\s+(-?\d+)\s*\)\s+\(\s*(-?\d+)\s+(-?\d+)\s*\)\s+\+ FIXED\s+\(\s*(-?\d+)\s+(-?\d+)\s*\) N\s*;')
    matches = list(pattern.finditer(pins[0][1])); cursor = 0; port_rows = {}
    for match in matches:
        need(not pins[0][1][cursor:match.start()].strip(), 'Unsupported far-row port syntax'); cursor = match.end()
        name, net, direction, *numbers = match.groups(); need(net in wanted and name not in port_rows, 'Duplicate/foreign far-row port')
        row = wanted[net]; half = row['width_DBU'] // 2; values = list(map(int,numbers))
        endpoint = 'start_DBU' if name == net+'_A' else 'end_DBU' if name == net+'_B' else None
        need(endpoint and direction == ('INPUT' if endpoint == 'start_DBU' else 'OUTPUT')
             and values == [-half,-half,half,half,*row[endpoint]], 'Actual port shape/layer/placement differs')
        port_rows[name] = values
    need(len(port_rows) == 36 and not pins[0][1][cursor:].strip(), 'Missing/unsupported far-row port')
    return dict(routes=actual, ports=port_rows, NDR=ndr, actual18nets36ports=True, no_routed_vias=True)
