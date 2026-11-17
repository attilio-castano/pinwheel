"""Issue a fresh HOST custody audit for a restored October 22 CAD runtime."""

import argparse
from pathlib import Path

import streaming_8x4_final_runtime as runtime


REQUEST = Path('final-cad-runtime-audit-01/request.json')
ASSEMBLY = Path('final-cad-runtime/assembly.json')
REPORT = Path('final-cad-runtime-audit-01/report.json')


def recorded_path(value):
    path = Path(value)
    runtime.need(path.is_absolute() and str(path) == value and '..' not in path.parts,
                 f'Invalid recorded runtime path: {value}')
    return path


def relocate(recovery, report_sha256, output):
    recovery = recovery.resolve(strict=True)
    report_path = recovery / REPORT
    runtime.need(runtime.digest(report_path) == report_sha256, 'Historical runtime audit hash mismatch')
    historical = runtime.read(report_path)
    runtime.need(historical.get('schema') == 'pinwheel.streaming-8x4-final-runtime-audit.v1'
                 and historical.get('passed') is True
                 and historical.get('executable_launched') is False
                 and historical.get('qualified') is False
                 and historical.get('tool_identity_unchanged') is True
                 and historical['tool_identity_before'] == historical['tool_identity_after']
                 and historical['cad_runtime_archive_membership']['cad_selected_archive_membership_verified'] is True,
                 'An exact, completed historical HOST runtime audit is required')

    old_request = recorded_path(historical['request']['path'])
    old_recovery = old_request.parents[1]
    runtime.need(old_request == old_recovery / REQUEST
                 and not recovery.is_relative_to(old_recovery)
                 and not old_recovery.is_relative_to(recovery),
                 'Restore the recovery tree to a separate directory')

    def mapped_path(value):
        path = recorded_path(value)
        return str(recovery / path.relative_to(old_recovery)) if path.is_relative_to(old_recovery) else value

    request_path = recovery / REQUEST
    request_sha256 = runtime.digest(request_path)
    runtime.need(request_sha256 == historical['request']['sha256'], 'Historical request hash mismatch')
    request = runtime.read(request_path)
    runtime.need(request['tools'] == historical['tools']
                 and request['producer_commit'] == historical['producer_commit']
                 and request['producer_sha256'] == historical['producer_sha256'],
                 'Historical audit and request disagree')

    assembly_path = recovery / ASSEMBLY
    assembly_sha256 = runtime.digest(assembly_path)
    runtime.need(recorded_path(request['assembly']['path']) == old_recovery / ASSEMBLY
                 and assembly_sha256 == request['assembly']['sha256'],
                 'Historical assembly path or hash mismatch')
    assembly = runtime.read(assembly_path)
    runtime.need(dict(assembly['tools'], **runtime.HOST_TOOLS) == request['tools'],
                 'Historical assembly and request disagree')
    tools = {name: mapped_path(path) for name, path in assembly['tools'].items()}
    cad_root = recovery / ASSEMBLY.parent
    runtime.need(all(Path(path).is_relative_to(cad_root) and
                     Path(path).resolve(strict=True).is_relative_to(cad_root)
                     for path in tools.values()), 'Relocated CAD tools must stay within the restored runtime')

    # Keep the historical receipts byte-identical. The fresh assembly includes
    # only current runtime paths and a hash binding back to the historical chain.
    output.mkdir()
    new_assembly = output / 'assembly.json'
    runtime.write(new_assembly, {
        'schema': assembly['schema'],
        'tools': tools,
        'executable_launched': False,
        'qualified': False,
        'historical_sha256': {'audit': report_sha256, 'request': request_sha256, 'assembly': assembly_sha256},
    })
    runtime.prepare(new_assembly, output / 'preparation')
    fresh_report = output / 'report.json'
    pending_report = output / 'pending-report.json'
    current = runtime.audit(output / 'preparation/request.json', pending_report)

    old_identity = historical['tool_identity_before']
    expected_identity = dict(old_identity,
        archives={mapped_path(path): digest for path, digest in old_identity['archives'].items()},
        files={mapped_path(path): dict(entry, resolved=mapped_path(entry['resolved']))
               for path, entry in old_identity['files'].items()})
    runtime.need(current['tool_identity_before'] == expected_identity,
                 'Fresh runtime identity differs from the historical identity after relocation')

    old_membership = historical['cad_runtime_archive_membership']
    expected_membership = dict(old_membership, packages={
        name: dict(package, install_directory=mapped_path(package['install_directory']),
                   archive=mapped_path(package['archive']))
        for name, package in old_membership['packages'].items()
    })
    runtime.need(current['cad_runtime_archive_membership'] == expected_membership,
                 'Fresh archive membership differs from the historical audit')
    pending_report.rename(fresh_report)
    return fresh_report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--recovery', type=Path, required=True, help='Restored recovery directory')
    parser.add_argument('--historical-report-sha256', required=True)
    parser.add_argument('--output', type=Path, required=True, help='New directory for the relocated audit')
    args = parser.parse_args()
    print(relocate(args.recovery, args.historical_report_sha256, args.output.resolve()))


if __name__ == '__main__':
    main()
