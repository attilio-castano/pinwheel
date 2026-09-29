#!/usr/bin/env python3
"""Check paired upload admission, ownership and packaged E64 proofs without CAD.

The default run needs only Python and the pinned Lean toolchain. An optional
retained mapping manifest adds byte-identity checks against historical artifacts;
it is not required for the proof checks and does not rerun physical qualification.
"""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import re
import time

from validation_run import Commands, fresh_directory, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--retained-manifest', type=Path)
    args = parser.parse_args()
    out = fresh_directory(ROOT / 'build/validation', args.tag)
    run = Commands(ROOT, out, default_timeout=300)
    started = time.monotonic()
    report = dict(schema=6, status='running', date=datetime.now(timezone.utc).isoformat(),
                  commands=run.records, cad_seconds=0,
                  scope='Exact paired graph, legal memory modes, accepted-upload ownership and '
                        'cycle-for-cycle E64 execution through the retained package adapters and result mailbox. '
                        'Three sampled reset-low edges and two idle release edges prepare arbitrary state. '
                        'A qualified serial begin/290-word/commit session for a certified image necessarily '
                        'passes admission and establishes the execution relation without another reset. '
                        'The decoded admission theorem also applies to stopped initialized replacements. '
                        'Segment inputs have init=0 and command!=3. '
                        'Loader sideband retains graph semantics. The SRAM law is explicit; RTL emission, '
                        'analog sampling, macro behavior and physical qualification remain separate.')
    sources = [ROOT / 'Pinwheel.lean', *sorted((ROOT / 'Pinwheel').rglob('*.lean')),
               *[ROOT / p for p in ['scripts/check-paired-formal.py', 'scripts/check-foundation.py',
                 'scripts/validation_run.py', 'scripts/process_group.py', 'test/PairedFormal.lean',
                 'test/PairedUpload.lean', 'test/PairedRuntime.lean', 'test/PairedTimed.lean', 'test/PairedHost.lean',
                 'test/PairedAdmission.lean',
                 'test/PairedGraph.lean', 'test/PairedSchedule.lean', 'test/ProofAudit.lean',
                 'test/PairedValidationEmit.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json']]]
    try:
        retained = {}
        if args.retained_manifest:
            manifest_path = args.retained_manifest.resolve()
            manifest = json.loads(manifest_path.read_text())
            previous_path = ROOT / manifest['report']
            if sha(previous_path) != manifest['report_sha256']:
                raise ValueError('Retained mapping report identity mismatch')
            previous = json.loads(previous_path.read_text())
            if manifest['status'] != 'passed' or previous['status'] != 'passed' or manifest['implementation'] != 'PairedValidation':
                raise ValueError('Expected passing PairedValidation mapping evidence')
            sources += [manifest_path, previous_path]
            for name in ['core.mlir', 'chip.mlir', 'assembly.json']:
                path = previous_path.parent / name
                digest = previous['artifact_sha256'][str(path.relative_to(ROOT))]
                if sha(path) != digest:
                    raise ValueError('Changed retained artifact: ' + str(path))
                retained[name] = dict(path=str(path.relative_to(ROOT)), sha256=digest)
                sources.append(path)
        report['source_sha256'] = {str(p.relative_to(ROOT)): sha(p) for p in sources}
        spec = importlib.util.spec_from_file_location('foundation', ROOT / 'scripts/check-foundation.py')
        foundation = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(foundation)
        report['reachable_modules'] = foundation.check_imports()
        version = run(['lake', 'env', 'lean', '--version'], 'version').strip()
        expected = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
        if not re.search(r'Lean \(version ' + re.escape(expected) + r'(?:,|\s)', version):
            raise ValueError('Wrong Lean toolchain: ' + version)
        report['lean'] = version
        run(['lake', 'build'], 'build')
        lean = ['lake', 'env', 'lean', '-DwarningAsError=true']
        audit = run([*lean, 'test/ProofAudit.lean'], 'axioms')
        counts = re.search(r'Pinwheel audit: (\d+) declarations, (\d+) theorems;', audit)
        if not counts:
            raise ValueError('Missing complete library axiom audit')
        report['audit'] = dict(declarations=int(counts[1]), theorems=int(counts[2]), standard_axioms_only=True)
        text = (ROOT / 'test/ProofAudit.lean').read_text()
        if not text.endswith('#audit_pinwheel\n'):
            raise ValueError('Missing audit mutation anchor')
        negative = out / 'RejectAxiom.lean'
        negative.write_text(text.removesuffix('#audit_pinwheel\n') +
                            'axiom Pinwheel.CI.untrusted : False\n#audit_pinwheel\n')
        run([*lean, negative], 'reject-untrusted-axiom', reject='Unapproved axioms in Pinwheel.CI.untrusted')
        witness = run([*lean, '--run', 'test/PairedFormal.lean', out], 'formal-witness')
        if 'both constructors pass; 45 nodes; proved package matches emitted package.' not in witness:
            raise ValueError('Missing exact package witness')
        report['contract_controls'] = dict(kernel_checked_examples=9, graph_nodes=45,
            arbitrary_initial_memory=True, write_holds_q=True, enabled_read_updates_q=True,
            idle_holds_q=True, undefined_read_unspecified=True, illegal_mode_excluded=True,
            reversed_and_duplicate_bindings_rejected=True)
        upload = run([*lean, '--run', 'test/PairedUpload.lean'], 'upload-controls')
        if 'Paired upload controls: retained core; two complete images;' not in upload:
            raise ValueError('Missing retained-controller upload controls')
        report['upload_controls'] = dict(retained_core=True, complete_images=2,
            arbitrary_initial_registers_contents_and_q=True,
            malformed_parameter_row_boot_idle_rejected=True,
            short_extra_busy_abort_reset_restart_controls=True,
            all_32_parameters_256_rows_boot_idle_checked=True,
            prior_active_bank_preserved=True, row_255_read_and_old_q_checked=True,
            initialization_invalidates_without_clearing=True)
        runtime = run([*lean, '--run', 'test/PairedRuntime.lean'], 'runtime-controls')
        runtime_counts = re.search(r'Paired runtime controls: retained core; certified image; both active banks; '
                                  r'(\d+) reference edges; (\d+) running edges; six scenarios; '
                                  r'stale-Q/parameter/token mutations rejected\.', runtime)
        if not runtime_counts:
            raise ValueError('Missing retained-controller runtime controls')
        report['runtime_controls'] = dict(retained_core=True, certified_image=True,
            loaded_through_actual_commands=True, both_active_banks=True,
            reference_edges=int(runtime_counts[1]), running_edges=int(runtime_counts[2]),
            scenarios=['capture/branch/qualify/halt', 'wait timeout', 'guard fault',
                       'false branch/out of range', 'qualify timeout', 'reset and restart'],
            pins_samples_modes_counters_and_running_pc_compared=True,
            stopped_q_holds=True, stale_q_wrong_parameter_invalid_token_rejected=True,
            scope='Finite execution controls; universal execution correspondence is proved separately in PairedTimed.')
        timed = run([*lean, '--run', 'test/PairedTimed.lean'], 'timed-controls')
        timed_counts = re.search(r'Paired timed controls: retained outputs; certified accepted transcripts; '
                                r'both active banks; (\d+) before/after edge pairs; six scenarios; '
                                r'(\d+) state/parameter mutations rejected\.', timed)
        if not timed_counts:
            raise ValueError('Missing retained-controller timed boundary controls')
        report['timed_controls'] = dict(retained_public_outputs=True, certified_accepted_transcripts=True,
            both_active_banks=True, before_after_edge_pairs=int(timed_counts[1]),
            rejected_mutations=int(timed_counts[2]),
            scenarios=['terminal capture/branch/entry overwrite and maximum duration',
                       'zero-budget wait timeout', 'zero-budget qualify timeout',
                       'guard beats zero-duration dispatch', 'reset beats start and command reset restarts',
                       'backward jump and repeated capture overwrite'],
            ready_at_wait_and_qualify_deadline_wins=True,
            scope='Finite controls, separate from the universal initialized-segment theorem.')
        report['timed_refinement'] = dict(
            theorem='Pinwheel.Hardware.Storage.PairedTimed.initialized_segment',
            arbitrary_initial_registers_contents_and_q=True,
            arbitrary_finite_execution_histories=True, before_and_after_every_edge=True,
            one_reference_edge_per_controller_edge=True,
            observations=['mode', 'pc', 'remaining', 'waitLeft', 'pin levels', 'pin enables', '16 samples'],
            premises=['explicit single-port SRAM contract', 'initializing edge',
                      'actual active bank valid after upload history',
                      'accepted active transcript passes source certificate',
                      'reset establishes execution relation',
                      'execution inputs have init=0 and command!=3'],
            package_and_host_execution_composition=False, physical_qualification=False)
        host = run([*lean, '--run', 'test/PairedHost.lean'], 'host-controls')
        host_counts = re.search(r'Paired host controls: retained package; both banks; (\d+) pin edge pairs; '
                               r'commit/start without reset; replacement retains mailbox; serial frames and pages; '
                               r'(\d+) executed mutations rejected\.', host)
        if not host_counts:
            raise ValueError('Missing retained-package lifecycle controls')
        report['host_controls'] = dict(retained_package=True, both_active_banks=True,
            before_after_pin_edge_pairs=int(host_counts[1]), rejected_mutations=int(host_counts[2]),
            arbitrary_initial_core_adapter_mailbox_and_sram_state=True,
            three_reset_low_edges=True, certified_accepted_staged_and_active_transcripts=True,
            decoded_uploads=2, serial_commit_frames=2, serial_start_frames=3,
            extra_reset_after_commit=False, immediate_decoded_start_checked=True,
            unread_result_survives_replacement=True, halt_only_completion_and_overrun=True,
            consume_clear_and_restart=True, low_high_result_pages=True,
            scope='Finite package controls prepare complete images via actual decoded writes; '
                  '290-word uploads are not replayed bit by bit. Serial delivery is proved separately.')
        report['package_refinement'] = dict(
            theorem='Pinwheel.Hardware.Storage.PairedHost.retained_initialized_commit_segment',
            delivery_theorem='Pinwheel.Hardware.Storage.PairedHost.session_delivers',
            arbitrary_initial_core_adapters_mailbox_contents_and_q=True,
            arbitrary_host_prefix_and_finite_execution_segments=True,
            before_and_after_every_edge=True, extra_reset_after_commit=False,
            certified_replacement_boundary=True, mailbox_may_start_occupied=True,
            all_three_package_output_ports=True, actual_sampler_and_receiver_edges=True,
            loader_sideband='Exact graph semantics; E64 replaces execution state and busy.',
            premises=['explicit single-port SRAM contract', 'three sampled reset-low edges',
                      'actual commit accepted after arbitrary host history',
                      'actual staged transcript passes source certificate',
                      'decoded execution inputs have init=0 and command!=3',
                      'qualified digital Serial.Session plus idle adapters for delivery theorem'],
            every_offered_certified_upload_admitted_proved=False,
            analog_sampling_or_physical_qualification=False)
        admission = run([*lean, '--run', 'test/PairedAdmission.lean'], 'admission-controls')
        admission_counts = re.search(r'Paired admission controls: retained core; two certified parameter permutations; '
                                     r'(\d+) accepted pushes; (\d+) quiet edges; (\d+) executed refusals; '
                                     r'(\d+) wrong-source certificates rejected; commit establishes E64 without reset\.', admission)
        if not admission_counts:
            raise ValueError('Missing retained-controller certified-admission controls')
        report['admission_controls'] = dict(retained_core=True, certified_parameter_permutations=2,
            accepted_pushes=int(admission_counts[1]), quiet_edges=int(admission_counts[2]),
            executed_refusals=int(admission_counts[3]), wrong_source_certificates_rejected=int(admission_counts[4]),
            both_banks=True, dirty_initial_storage=True, unused_parameters_noncanonical_for_tokens=True,
            all_parameters_rows_and_metadata_checked=True, previous_active_image_preserved=True,
            no_extra_reset_after_commit=True,
            scope='Finite decoded-command controls; qualified full serial admission is proved universally. '
                  'The new harness does not replay 290 words bit by bit.')
        report['admission_refinement'] = dict(
            theorem='Pinwheel.Hardware.Storage.PairedSession.retained_initialized_session',
            decoded_theorem='Pinwheel.Hardware.Storage.PairedSession.upload_admitted',
            arbitrary_initial_core_adapters_mailbox_contents_and_q=True,
            every_certified_upload_admitted=True, arbitrary_quiet_gaps=True,
            admission_decisions_and_accepted_transcript_derived=True,
            inactive_parameter_table_owned_before_row_validation=True,
            stopped_initialized_replacement_supported=True, extra_reset_after_commit=False,
            before_and_after_every_execution_edge=True, all_three_package_output_ports=True,
            loader_sideband='Exact graph semantics; E64 replaces execution state and busy.',
            premises=['explicit single-port SRAM contract', 'three reset-low samples and two idle release samples',
                      'image corresponds to canonical E64 source', 'qualified digital Serial.Session',
                      'two trailing sampler-drain pins', 'decoded execution inputs have init=0 and command!=3'],
            full_290_word_serial_upload_replayed_by_new_finite_test=False,
            rtl_emission_or_physical_qualification=False)
        run([*lean, '--run', 'test/PairedGraph.lean'], 'graph-controls')
        run([*lean, 'test/PairedSchedule.lean'], 'schedule')
        emitted = out / 'emitted'
        run([*lean, '--run', 'test/PairedValidationEmit.lean', emitted], 'emit')
        if sha(out / 'proved-chip.mlir') != sha(emitted / 'chip.mlir'):
            raise ValueError('Package witness differs from standalone emitter')
        report['retained_artifacts'] = retained
        for name, entry in retained.items():
            if sha(emitted / name) != entry['sha256']:
                raise ValueError('Fresh emission differs from retained artifact: ' + name)
        report['retained_identity_checked'] = bool(retained)
        report['status'] = 'passed'
    except BaseException as error:
        report.update(status='failed', error=f'{type(error).__name__}: {error}')
        raise
    finally:
        report['seconds'] = round(time.monotonic() - started, 3)
        report['inputs_unchanged'] = all(sha(ROOT / path) == digest
                                       for path, digest in report.get('source_sha256', {}).items())
        if not report['inputs_unchanged']:
            report['status'] = 'failed'
        report['artifact_sha256'] = {str(p.relative_to(ROOT)): sha(p)
                                    for p in sorted(out.rglob('*')) if p.is_file()}
        with (out / 'report.json').open('x') as stream:
            stream.write(json.dumps(report, indent=2) + '\n')
        print(json.dumps({k: report.get(k) for k in ['status', 'seconds', 'audit', 'retained_identity_checked', 'error']}), flush=True)
    if report['status'] != 'passed':
        raise RuntimeError('Paired formal check failed')


if __name__ == '__main__':
    main()
