"""Carry all qualified source/session APIs through actual mapped components.

The factory reuses ordinary proof bodies; every new declaration is compiled
against fresh mapped component, actual package and mapped pad certificates.
"""
import streaming_uart_composition


def generate(addr_bits):
    if type(addr_bits) is not int or addr_bits not in (1,2):
        raise ValueError('Mapped composition requires queue address width1 or2')
    depth=str(2**addr_bits)
    previous='StreamingUARTSessionD'+depth
    current='StreamingMappedSessionD'+depth
    source=streaming_uart_composition.generate(addr_bits)[previous]
    replacements={
        'import ReadyCoreD'+depth+'Proof':'import MappedCoreD'+depth+'Proof',
        'import ReadyQuadFrontendProof':'import MappedFrontendProof',
        'import StreamingReadyWrappersD'+depth:'import StreamingMappedPackageD'+depth+'\nimport StreamingMappedTinyD'+depth,
        'Pinwheel.Artifact.'+previous:'Pinwheel.Artifact.'+current,
        'Pinwheel.Artifact.StreamingReadyFrontend.':'Pinwheel.Artifact.StreamingMappedFrontend.',
        'Pinwheel.Artifact.StreamingReadyCoreD'+depth+'.':'Pinwheel.Artifact.StreamingMappedCoreD'+depth+'.',
        'Pinwheel.Artifact.StreamingReadyWrappersD'+depth+'.actualPackage':
            'Pinwheel.Artifact.StreamingMappedPackageD'+depth+'.actualPackage',
        'Pinwheel.Artifact.StreamingReadyWrappersD'+depth+'.package_correct':
            'Pinwheel.Artifact.StreamingMappedPackageD'+depth+'.package_correct',
        'Pinwheel.Artifact.StreamingReadyWrappersD'+depth+'.actualTiny':
            'Pinwheel.Artifact.StreamingMappedTinyD'+depth+'.actualTiny',
        'Pinwheel.Artifact.StreamingReadyWrappersD'+depth+'.tiny_correct':
            'Pinwheel.Artifact.StreamingMappedTinyD'+depth+'.tiny_correct',
    }
    for old,new in replacements.items():
        if old not in source: raise RuntimeError('Inherited proof factory boundary changed: '+old)
        source=source.replace(old,new)
    if 'StreamingReadyWrappers' in source or 'import ReadyCore' in source or 'import ReadyQuadFrontend' in source:
        raise RuntimeError('Mapped physical factory retained an unmapped artifact import')
    return {current:source}
