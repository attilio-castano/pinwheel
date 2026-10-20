"""Explicit nominal wire RC and native verification for TT timing diagnostics.

The pinned CMOS5L config has an empty LAYERS_RC dictionary. Derive its nominal
values from the actual tech LEF; do not silently interpret missing values as
zero-wire timing. These estimates do not qualify extracted min/max RC corners.
"""
from physical_route_intake import ihp_layer_rc

CORNERS = ('nom_fast_1p32V_m40C','nom_slow_1p08V_125C','nom_typ_1p20V_25C')


def validate_nominal_rc(config, tech_lef):
    expected = ihp_layer_rc(tech_lef)
    if config.get('LAYERS_RC') != expected:
        raise ValueError('Explicit nominal layer RC differs from actual pinned LEF')
    if config.get('RT_MAX_LAYER') != 'Metal4':
        raise ValueError('Signal routing exceeds declared TT Metal4 limit')
    return dict(layer_rc=expected, units=dict(res='kohm/um',cap='pF/um'),
        liberty_corners=list(CORNERS), rc_corners=['nominal'],
        extracted=False, min_max_rc_qualified=False,
        boundary='Nominal LEF defaults for placement/global-route estimates; extracted route acceptance is separate.')


def native_rc_guard():
    """Check every actual native corner/layer against the loaded tech LEF."""
    return '\n'.join([
        'set pw_rc_corners {}',
        'foreach {corner_name corner} [lln::get_corner_dict] {',
        '  lappend pw_rc_corners $corner_name',
        '  foreach layer [[ord::get_db_tech] getLayers] {',
        '    if {[$layer getType] ne "ROUTING"} {continue}',
        '    lassign [est::dblayer_wire_rc $layer] default_r default_c',
        '    set actual_r [est::layer_resistance $layer $corner]',
        '    set actual_c [est::layer_capacitance $layer $corner]',
        '    if {$default_r <= 0 || $default_c <= 0 || abs($actual_r / $default_r - 1) > 1e-6 || abs($actual_c / $default_c - 1) > 1e-6} {error "Explicit layer RC differs from nominal LEF"}',
        '    puts "PINWHEEL_STREAMING_NOMINAL_RC $corner_name [$layer getName] $actual_r $actual_c"',
        '  }',
        '}',
        'if {[lsort $pw_rc_corners] ne [list ' + ' '.join(sorted(CORNERS)) + ']} {error "Wrong native TT corner inventory"}',
        'puts "PINWHEEL_STREAMING_NOMINAL_RC_VERIFIED"',''])
