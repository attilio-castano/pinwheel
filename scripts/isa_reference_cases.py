"""Raw integer encodings, independent of Pinwheel's decoder/encoder/semantics."""
import random

MASK = (1 << 32) - 1
KINDS = ("lui auipc jal jalr beq bne blt bge bltu bgeu lb lh lw lbu lhu sb sh sw "
         "addi slti sltiu xori ori andi slli srli srai add sub sll slt sltu xor srl sra or and fence ecall ebreak").split()


def imm(opcode, funct, rd, rs, value):
    return ((value & 4095) << 20) | (rs << 15) | (funct << 12) | (rd << 7) | opcode


def reg(funct, high, rd, left, right):
    return (high << 25) | (right << 20) | (left << 15) | (funct << 12) | (rd << 7) | 0x33


def branch(funct, left, right, offset):
    x = offset & 8191
    return ((x >> 12) << 31) | (((x >> 5) & 63) << 25) | (right << 20) | (left << 15) | (funct << 12) | (((x >> 1) & 15) << 8) | (((x >> 11) & 1) << 7) | 0x63


def jump(rd, offset):
    x = offset & 0x1fffff
    return ((x >> 20) << 31) | (((x >> 1) & 1023) << 21) | (((x >> 11) & 1) << 20) | (((x >> 12) & 255) << 12) | (rd << 7) | 0x6f


def store(funct, base, operand, offset):
    x = offset & 4095
    return ((x >> 5) << 25) | (operand << 20) | (base << 15) | (funct << 12) | ((x & 31) << 7) | 0x23


LOADS = dict(lb=0, lh=1, lw=2, lbu=4, lhu=5)
STORES = dict(sb=0, sh=1, sw=2)
BRANCHES = dict(beq=0, bne=1, blt=4, bge=5, bltu=6, bgeu=7)
IMMEDIATES = dict(addi=0, slti=2, sltiu=3, xori=4, ori=6, andi=7)
REGISTERS = dict(add=(0, 0), sub=(0, 32), sll=(1, 0), slt=(2, 0), sltu=(3, 0), xor=(4, 0), srl=(5, 0), sra=(5, 32), or_=(6, 0), and_=(7, 0))


def campaign():
    cases = []
    rng = random.Random(0x5341494C)

    def add(kind, word, registers, *, pc=0x100, feature="base"):
        assert 0 <= word <= MASK and 0 <= pc <= 4092 and pc % 4 == 0
        registers = [x & MASK for x in registers]
        registers[0] = 0
        i = len(cases)
        ram = [((k * 31) ^ (k >> 3) ^ (i * 17) ^ 0x80) % 256 for k in range(4096)]
        cases.append(dict(id=i, kind=kind, feature=feature, pc=pc, word=word, registers=registers, ram=ram))

    values = [0, 1, 0x7fffffff, 0x80000000, MASK, 0x89abcdef, 31, 32]
    for kind in KINDS:
        for n, value in enumerate(values):
            registers = [rng.getrandbits(32) for _ in range(32)]
            left, right, dest = 1, 2, [3, 0, 1, 2, 31, 3, 0, 3][n]
            registers[left] = value
            registers[right] = values[(n + 3) % len(values)]
            immediate = [-2048, -1, 0, 1, 2047, -17, 31, 0][n]
            pc = [0, 4, 0x100, 0xffc][n % 4]
            if kind == "lui": word = ((value & 0xfffff) << 12) | (dest << 7) | 0x37
            elif kind == "auipc": word = ((value & 0xfffff) << 12) | (dest << 7) | 0x17
            elif kind == "jal": word = jump(dest, [-1048576, -4, 0, 2, 4, 1048574, 8, -2][n])
            elif kind == "jalr":
                registers[left] = [0x200, 0x201, 0x202, 0x203, MASK, 0, 0x301, 0x10003][n]
                word = imm(0x67, 0, dest, left, [0, 0, 0, 0, 1, -1, -1, 0][n])
            elif kind in BRANCHES:
                pairs = [(0,0), (0,1), (1,0), (0x80000000,0x7fffffff), (MASK,0), (1,1), (0,0), (0,1)]
                registers[left], registers[right] = pairs[n]
                word = branch(BRANCHES[kind], left, right, [4, 4, -4, 4, 4094, -4096, 2, 2][n])
            elif kind in LOADS:
                width = {0:1,1:2,2:4,4:1,5:2}[LOADS[kind]]
                offset = (n * width) % 32
                registers[left] = 0x10000 + offset - immediate
                word = imm(0x03, LOADS[kind], dest, left, immediate)
            elif kind in STORES:
                width = 1 << STORES[kind]
                registers[left] = 0x10000 + (n*width) % 32 - immediate
                word = store(STORES[kind], left, right, immediate)
            elif kind in IMMEDIATES: word = imm(0x13, IMMEDIATES[kind], dest, left, immediate)
            elif kind in ("slli", "srli", "srai"):
                amount = [0, 1, 31, 16, 5, 30, 2, 17][n]
                word = imm(0x13, 1 if kind == "slli" else 5, dest, left, amount + (1024 if kind == "srai" else 0))
            elif kind in ("fence", "ecall", "ebreak"):
                word = ([0x0000000f, 0x0ff0000f, 0x8330000f, 0x0100000f,
                         0xfffF8f8f, 0x0010808f, 0xf000000f, 0x000f8f8f][n]
                        if kind == "fence" else (0x73 if kind == "ecall" else 0x100073))
            else:
                funct, high = REGISTERS[kind + "_" if kind in ("or", "and") else kind]
                registers[right] = [0,1,31,32,63,MASK,0x80000000,0x8000001f][n]
                word = reg(funct, high, dest, left, right)
            add(kind, word, registers, pc=pc, feature="boundaries_overlap_x0")

    # Data alignment wins over access failure; x0 loads still issue/fault.
    for kind, funct in {**LOADS, **STORES}.items():
        for address in [0x10000, 0x10fff, 0x11000, 0x11001, 0x20000, 0x20001, 0, 4095, 4096, MASK]:
            registers = [rng.getrandbits(32) for _ in range(32)]
            registers[1] = address
            word = imm(3,funct,0,1,0) if kind in LOADS else store(funct,1,2,0)
            add(kind,word,registers,feature="data_fault_priority_x0")

    # Effective-address wrap is checked before mapping. No truncation aliases.
    for kind, funct in LOADS.items():
        registers = [rng.getrandbits(32) for _ in range(32)]
        registers[1] = MASK
        add(kind,imm(3,funct,3,1,1),registers,feature="effective_address_wrap_to_rom")

    for word in [0, 0xffffffff, 0x02001013, 0x40001013, 0x02005013, 0x60005013,
                 0x00001067, 0x00003003, 0x00007003, 0x00003023,
                 0x00002063, 0x00003063, 0x02000033, 0x0000100f, 0x00000053]:
        add("illegal",word,[rng.getrandbits(32) for _ in range(32)],feature="reserved_or_disabled_extension")

    for n in range(128):
        kind = list(IMMEDIATES)[n % 6] if n % 2 else list(REGISTERS)[n % 10]
        registers = [rng.getrandbits(32) for _ in range(32)]
        rd, left, right = rng.randrange(32), rng.randrange(32), rng.randrange(32)
        if kind in IMMEDIATES: word = imm(0x13,IMMEDIATES[kind],rd,left,rng.randrange(-2048,2048))
        else:
            funct,high = REGISTERS[kind];word=reg(funct,high,rd,left,right)
        add(kind.rstrip("_"),word,registers,feature="seeded_register_permutations")
    assert set(KINDS).issubset({c["kind"] for c in cases})
    return cases


EXCLUSIONS = [
    "MMIO register values/effects and device timing: Sail's platform differs; no GPIO/timer/UART equivalence claim.",
    "Privilege, CSRs, interrupts, WFI/MRET/SRET and optional extensions: project excludes them; Sail retains machine trap machinery.",
    "Concurrent FENCE ordering: only serialized architectural state/no-memory-change is compared; Pinwheel's fence-all acknowledgement is stronger.",
    "Fetch faults/current-PC misalignment and PC wrap at 0xfffffffc: this campaign begins at a valid aligned ROM fetch; no frontend comparison.",
    "Reset, loading, cycle counts, RAM handshake timing, RTL, synthesis and physical behavior: architectural comparison only.",
]
