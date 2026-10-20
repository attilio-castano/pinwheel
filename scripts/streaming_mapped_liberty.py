"""Restricted Boolean interpretation of the pinned mapped-cell library.

This is parser/interpreter groundwork, not an equivalence certificate or an
electrical model. Timing, power and analog behavior are outside this module.
"""
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re

LIBRARY_SHA256 = '34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad'
PREFIX = 'sg13cmos5l_'
FF = PREFIX + 'dfrbpq_1'
SUPPORTED = frozenset(PREFIX + suffix for suffix in (
    'a21o_1', 'a21oi_1', 'a221oi_1', 'a22oi_1', 'and2_1', 'and3_1', 'and4_1',
    'buf_1', 'dfrbpq_1', 'inv_1', 'mux2_1', 'mux4_1', 'nand2_1', 'nand2b_1',
    'nand3_1', 'nand3b_1', 'nand4_1', 'nor2_1', 'nor2b_1', 'nor3_1', 'nor4_1',
    'o21ai_1', 'or2_1', 'or3_1', 'or4_1', 'xnor2_1', 'xor2_1'))
IDENTIFIER = re.compile(r'[A-Za-z_][A-Za-z0-9_]*\Z')


def require(value, message):
    if not value: raise ValueError(message)


def parse_boolean(text, names):
    """Only identifiers,0/1,prefix!,*,^,+ and parentheses; full consumption.

    Precedence is NOT, AND, XOR, OR. No implicit AND, postfix inversion, bus
    syntax, arbitrary Python evaluation or unsupported-token fallback exists.
    """
    require(type(text) is str and text.strip(), 'Empty Boolean function')
    tokens, at = [], 0
    while at < len(text):
        if text[at].isspace(): at += 1; continue
        match = re.match(r'[A-Za-z_][A-Za-z0-9_]*|[01!()*+^]', text[at:])
        require(match is not None, 'Unsupported Boolean token')
        tokens.append(match[0]); at += len(match[0])
    position = 0
    def primary():
        nonlocal position
        require(position < len(tokens), 'Missing Boolean operand')
        token = tokens[position]; position += 1
        if token == '!': return ('not', primary())
        if token == '(':
            value = expression(0)
            require(position < len(tokens) and tokens[position] == ')', 'Unclosed Boolean group')
            position += 1
            return value
        if token in ('0', '1'): return ('constant', token == '1')
        require(IDENTIFIER.fullmatch(token) is not None and token in names, 'Unknown Boolean pin or state name: ' + token)
        return ('variable', token)
    def expression(level):
        nonlocal position
        if level == 3: return primary()
        operators = ('+', '^', '*')
        node = expression(level + 1)
        while position < len(tokens) and tokens[position] == operators[level]:
            operator = tokens[position]; position += 1
            node = (operator, node, expression(level + 1))
        return node
    result = expression(0)
    require(position == len(tokens), 'Trailing or implicit Boolean operator')
    return result


def eval_boolean(node, values):
    kind = node[0]
    if kind == 'constant': return node[1]
    if kind == 'variable':
        value = values[node[1]]
        require(type(value) is bool, 'Boolean pin values must be bool')
        return value
    if kind == 'not': return not eval_boolean(node[1], values)
    left, right = eval_boolean(node[1], values), eval_boolean(node[2], values)
    if kind == '*': return left and right
    if kind == '+': return left or right
    if kind == '^': return left != right
    raise ValueError('Unknown Boolean AST operation')


@dataclass(frozen=True)
class Token:
    text: str
    quoted: bool = False


def tokenize(text):
    result, at = [], 0
    while at < len(text):
        if text[at].isspace(): at += 1; continue
        if text.startswith('/*', at):
            end = text.find('*/', at + 2)
            require(end >= 0, 'Unclosed Liberty comment')
            at = end + 2; continue
        if text.startswith('//', at):
            end = text.find('\n', at + 2)
            at = len(text) if end < 0 else end + 1; continue
        if text[at] == '"':
            at += 1; value = []
            while at < len(text) and text[at] != '"':
                if text[at] == '\\':
                    require(at + 1 < len(text), 'Truncated Liberty string escape')
                    value.extend(text[at:at + 2]); at += 2
                else: value.append(text[at]); at += 1
            require(at < len(text), 'Unclosed Liberty string')
            at += 1; result.append(Token(''.join(value), True)); continue
        if text[at] in '{}():;,':
            result.append(Token(text[at])); at += 1; continue
        end = at
        while end < len(text) and not text[end].isspace() and text[end] not in '{}():;,"': end += 1
        require(end > at, 'Unsupported Liberty token')
        result.append(Token(text[at:end])); at = end
    return result


@dataclass(frozen=True)
class Item:
    name: str
    kind: str
    arguments: tuple = ()
    value: tuple = ()
    children: tuple = ()


def parse_document(text):
    tokens, at = tokenize(text), 0
    def items(nested):
        nonlocal at
        result = []
        while at < len(tokens) and tokens[at].text != '}':
            token = tokens[at]; at += 1
            require(not token.quoted and IDENTIFIER.fullmatch(token.text), 'Invalid Liberty statement name')
            name = token.text
            require(at < len(tokens), 'Truncated Liberty statement')
            next_token = tokens[at].text; at += 1
            if next_token == ':':
                values = []
                while at < len(tokens) and tokens[at].text != ';':
                    require(tokens[at].quoted or tokens[at].text not in ('{', '}'), 'Malformed Liberty attribute')
                    values.append(tokens[at]); at += 1
                require(at < len(tokens) and values, 'Truncated or empty Liberty attribute')
                at += 1; result.append(Item(name, 'attribute', value=tuple(values)))
            else:
                require(next_token == '(', 'Unsupported Liberty statement syntax')
                arguments, argument, depth = [], [], 1
                while at < len(tokens) and depth:
                    token = tokens[at]; at += 1
                    if not token.quoted and token.text == '(':
                        depth += 1
                    elif not token.quoted and token.text == ')':
                        depth -= 1
                        if depth == 0:
                            if argument or arguments: arguments.append(tuple(argument))
                            break
                    if not token.quoted and token.text == ',' and depth == 1:
                        arguments.append(tuple(argument)); argument = []
                    else: argument.append(token)
                require(depth == 0 and at < len(tokens), 'Unclosed Liberty argument list')
                terminator = tokens[at].text; at += 1
                require(terminator in ('{', ';'), 'Unsupported Liberty group terminator')
                children = items(True) if terminator == '{' else ()
                result.append(Item(name, 'group' if terminator == '{' else 'complex', tuple(arguments), children=tuple(children)))
        if nested:
            require(at < len(tokens) and tokens[at].text == '}', 'Unclosed Liberty group')
            at += 1
        return result
    result = items(False)
    require(at == len(tokens), 'Trailing Liberty document tokens')
    return result


def scalar(items, name, *, required=True):
    values = [item for item in items if item.name == name]
    require(len(values) == (1 if required else min(len(values), 1)), 'Missing or duplicate Liberty attribute: ' + name)
    if not values: return None
    require(values[0].kind == 'attribute' and len(values[0].value) == 1, 'Unsupported Liberty attribute value: ' + name)
    value = values[0].value[0].text
    require('\\' not in value, 'Escaped semantic Liberty attribute is unsupported')
    return value


def group_name(item):
    require(item.kind == 'group' and len(item.arguments) == 1 and len(item.arguments[0]) == 1,
        'Expected one scalar Liberty group name')
    name = item.arguments[0][0].text
    require(IDENTIFIER.fullmatch(name), 'Invalid Liberty group identifier')
    return name


@dataclass(frozen=True)
class Cell:
    name: str
    directions: dict
    output: str
    function_text: str
    function: tuple
    sequential: bool = False
    state_names: tuple = ()
    clocked_on: tuple | None = None
    next_state: tuple | None = None
    clear: tuple | None = None


@dataclass(frozen=True)
class Library:
    sha256: str
    cells: dict
    pinned: bool


def parse_library(text, used_cells=None):
    """Low-level parser also accepts synthetic test text; pinned marks provenance."""
    require(type(text) is str, 'Expected Liberty source text')
    selected = SUPPORTED if used_cells is None else set(used_cells)
    require(selected and selected <= SUPPORTED, 'Unsupported mapped-cell selection')
    roots = parse_document(text)
    require(len(roots) == 1 and roots[0].name == 'library' and roots[0].kind == 'group', 'Expected one Liberty library')
    candidates = {}
    for item in roots[0].children:
        if item.name != 'cell': continue
        name = group_name(item)
        require(name not in candidates, 'Duplicate Liberty cell')
        candidates[name] = item
    require(selected <= candidates.keys(), 'Selected mapped cell absent from Liberty')
    cells = {}
    for name in sorted(selected):
        item = candidates[name]
        require(all(child.name in ('pin', 'ff', 'leakage_power') for child in item.children if child.kind == 'group'),
            'Unsupported functional Liberty cell group')
        pins, directions, functions = {}, {}, {}
        for pin in [child for child in item.children if child.name == 'pin']:
            pin_name = group_name(pin)
            require(pin_name not in pins, 'Duplicate Liberty pin')
            pins[pin_name] = pin
            direction = scalar(pin.children, 'direction')
            require(direction in ('input', 'output'), 'Unsupported Liberty pin direction')
            require(not any(child.name in ('three_state', 'state_function') for child in pin.children),
                'Unsupported three-state or alternate state function')
            require(all(child.name in ('timing', 'internal_power') for child in pin.children if child.kind == 'group'),
                'Unsupported functional pin group')
            directions[pin_name] = direction
            if direction == 'output': functions[pin_name] = scalar(pin.children, 'function')
            else: require(scalar(pin.children, 'function', required=False) is None, 'Input pin unexpectedly has a function')
        require(len(functions) == 1, 'Exactly one Boolean output is supported per mapped cell')
        output, function_text = next(iter(functions.items()))
        ff = [child for child in item.children if child.name == 'ff']
        if name == FF:
            require(len(ff) == 1 and ff[0].kind == 'group' and ff[0].arguments ==
                ((Token('IQ'),), (Token('IQN'),)), 'Unsupported sequential state variables')
            require(directions == dict(Q='output', CLK='input', D='input', RESET_B='input') and output == 'Q',
                'Unsupported sequential pin inventory')
            require({child.name for child in ff[0].children} == {'clear', 'clocked_on', 'next_state'},
                'Unsupported preset, sequential group or additional FF control')
            clock = parse_boolean(scalar(ff[0].children, 'clocked_on'), {'CLK'})
            next_state = parse_boolean(scalar(ff[0].children, 'next_state'), {'D'})
            clear = parse_boolean(scalar(ff[0].children, 'clear'), {'RESET_B'})
            require(clock == ('variable', 'CLK') and next_state == ('variable', 'D') and
                clear == ('not', ('variable', 'RESET_B')) and function_text == 'IQ', 'Unsupported FF behavior')
            require(scalar(pins['CLK'].children, 'clock') == 'true' and all(
                scalar(pin.children, 'clock', required=False) is None for key, pin in pins.items() if key != 'CLK'),
                'Unsupported sequential clock pin declaration')
            cells[name] = Cell(name, directions, output, function_text, parse_boolean(function_text, {'IQ'}),
                True, ('IQ', 'IQN'), clock, next_state, clear)
        else:
            require(not ff and all(scalar(pin.children, 'clock', required=False) is None for pin in pins.values()),
                'Combinational cell has clock/state behavior')
            inputs = {pin for pin, direction in directions.items() if direction == 'input'}
            cells[name] = Cell(name, directions, output, function_text, parse_boolean(function_text, inputs))
    digest = hashlib.sha256(text.encode()).hexdigest()
    return Library(digest, cells, digest == LIBRARY_SHA256)


def load_library(path, used_cells=None):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Expected a regular pinned Liberty file')
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == LIBRARY_SHA256, 'Refuse an unpinned mapped-cell Liberty')
    return parse_library(data.decode('utf-8'), used_cells)
