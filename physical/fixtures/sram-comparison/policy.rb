# Experimental comparison preparation; extraction and source GDS remain unchanged.
require 'json'
pw_path = ENV.fetch('PINWHEEL_POLICY_REPORT')
pw_contract = JSON.parse(File.read(ENV.fetch('PINWHEEL_POLICY_CONTRACT')))
pw_top_name = src.cell_name
pw_audit = {'policy' => 'physical-boundary-and-dimensional-resistors-v4',
            'top' => pw_top_name, 'stages' => {}, 'status' => 'running'}
pw_save = lambda { File.write(pw_path, JSON.pretty_generate(pw_audit) + "\n") }
pw_require = lambda do |ok, message|
  unless ok
    pw_audit['status'] = 'rejected'
    pw_audit['reason'] = message
    pw_save.call
    raise "PINWHEEL_POLICY_REJECT: #{message}"
  end
end
pw_spec = pw_contract['tops'][pw_top_name]
pw_require.call(!pw_spec.nil?, 'Unsupported fixture top')
pw_require.call(!NET_ONLY && !IGNORE_TOP_PORTS_MISMATCH, 'Comparison or strict-port checking disabled')

pw_ports = lambda do |circuit|
  pw_require.call(!circuit.nil?, 'Missing top circuit')
  circuit.each_pin.map do |pin|
    wire = circuit.net_for_pin(pin.id)
    {'id' => pin.id, 'name' => pin.name, 'net' => wire.nil? ? nil : wire.name,
     'device_terminals' => wire.nil? ? 0 : wire.terminal_count,
     'child_pins' => wire.nil? ? 0 : wire.subcircuit_pin_count}
  end
end
pw_reference_ports = lambda do |stage|
  rows = pw_ports.call(schematic.circuit_by_name(pw_top_name))
  pw_audit['stages'][stage] = {'schematic_ports' => rows}
  pw_require.call(rows.map { |r| r['name'] } == pw_spec['ports'], 'Declared port identity/order changed')
  rows.each do |row|
    pw_require.call(row['device_terminals'] + row['child_pins'] > 0,
                    "Disconnected declared port #{row['name']}")
  end
  rows
end

pw_expanded = nil
pw_expanded = lambda do |circuit, stack|
  pw_require.call(!stack.include?(circuit.name), 'Recursive circuit hierarchy')
  models = Hash.new(0)
  resistors = []
  circuit.each_device do |device|
    model = device.device_class.name.downcase
    pw_require.call(pw_contract['allowed_models'].include?(model), "Unsupported active model #{model}")
    models[model] += 1
    if model == 'res_metal1'
      width = device.parameter('W'); length = device.parameter('L')
      pw_require.call(width.finite? && length.finite? && width > 0 && length > 0,
                      'Missing or invalid resistor dimensions')
      resistors << [width, length]
    end
  end
  circuit.each_subcircuit do |instance|
    child = pw_expanded.call(instance.circuit_ref, stack + [circuit.name])
    child['models'].each { |model, count| models[model] += count }
    resistors.concat(child['resistors'])
  end
  {'models' => models.sort.to_h, 'resistors' => resistors.sort}
end

pw_reference_ports.call('before_preparation')
# Read only labels owned by the fixture boundary, before hierarchy is removed.
# Child A/Z labels denote internal wires when this cell is instantiated.
pw_source = RBA::Layout.new
pw_source.read($input)
pw_cell = pw_source.cell(pw_top_name)
pw_require.call(!pw_cell.nil?, 'Missing source top cell')
pw_layout_top = netlist.circuit_by_name(pw_top_name)
pw_require.call(!pw_layout_top.nil?, 'Missing extracted top circuit')
pw_require.call(pw_layout_top.each_pin.to_a.empty?, 'Unexpected pre-existing top pins')
pw_witnesses = []
pw_regions = {'8/2' => metal1_con.data, '8/25' => metal1_con.data,
              '30/25' => metal3_con.data}
pw_source.layer_indexes.each do |index|
  info = pw_source.get_info(index)
  layer = "#{info.layer}/#{info.datatype}"
  next unless pw_regions.key?(layer)
  pw_cell.shapes(index).each do |shape|
    next unless shape.is_text?
    label = shape.text
    name = {'VDD!' => 'VDD', 'VSS!' => 'VSS'}.fetch(label.string, label.string)
    pw_witnesses << {'name' => name, 'source_name' => label.string, 'layer' => layer,
                     'x_um' => label.x * pw_source.dbu, 'y_um' => label.y * pw_source.dbu}
  end
end
pw_audit['physical_port_witnesses'] = pw_witnesses
pw_require.call(pw_witnesses.map { |w| w['name'] }.sort == pw_spec['ports'].sort,
                'Physical boundary labels missing, duplicated, extra or renamed')
pw_bindings = {}
pw_wire_key = lambda { |wire| [wire.circuit.name, wire.cluster_id] }
pw_witnesses.each do |witness|
  path = []
  wire = l2n_data.probe_net(pw_regions[witness['layer']],
    RBA::DPoint.new(witness['x_um'], witness['y_um']), path, pw_layout_top)
  pw_require.call(!wire.nil? && wire.circuit == pw_layout_top && path.empty?,
                  "Boundary label does not probe a top net: #{witness['name']}")
  pw_require.call(wire.terminal_count + wire.subcircuit_pin_count > 0,
                  "Disconnected physical port #{witness['name']}")
  pw_require.call(!pw_bindings.values.any? { |bound| pw_wire_key.call(bound) == pw_wire_key.call(wire) }, 'Two physical ports probe the same net')
  pw_require.call(wire.cluster_id > 0, 'Unidentified physical net')
  witness['extracted_name'] = wire.name
  witness['cluster_id'] = wire.cluster_id
  pw_bindings[witness['name']] = wire
end
pw_flat = {}
[['layout', netlist], ['schematic', schematic]].each do |label, target|
  circuit = target.circuit_by_name(pw_top_name)
  pw_require.call(!circuit.nil?, "Missing #{label} top circuit")
  before = pw_expanded.call(circuit, [])
  target.each_device_class do |device_class|
    next unless device_class.name.downcase == 'res_metal1'
    device_class.enable_parameter('W', true)
    device_class.enable_parameter('L', true)
    device_class.enable_parameter('R', false)
    device_class.supports_serial_combination = false
    device_class.supports_parallel_combination = false
  end
  target.flatten
  after = pw_expanded.call(target.circuit_by_name(pw_top_name), [])
  pw_require.call(before == after, "Flattening changed #{label} expanded devices/dimensions")
  pw_audit['stages'][label + '_flatten'] = {'before' => before, 'after' => after}
  pw_flat[label] = after
end
pw_reference_ports.call('after_flatten')
pw_layout_top = netlist.circuit_by_name(pw_top_name)
pw_spec['ports'].each do |name|
  wire = pw_bindings.fetch(name)
  pw_require.call(!wire._destroyed? && wire.circuit == pw_layout_top && wire.terminal_count > 0,
                  "Flattening lost physical port #{name}")
  other = pw_layout_top.net_by_name(name)
  pw_require.call(other.nil? || pw_wire_key.call(other) == pw_wire_key.call(wire), "Physical port name collision #{name}")
  pw_require.call(pw_layout_top.each_net.count { |n| pw_wire_key.call(n) == pw_wire_key.call(wire) } == 1, 'Ambiguous physical net identity')
  # Annotate the existing extracted net; never reconnect a device terminal.
  terminals = wire.terminal_count
  wire.name = name
  pin = pw_layout_top.create_pin(name)
  pw_layout_top.connect_pin(pin.id, wire)
  pw_require.call(wire.terminal_count == terminals, 'Boundary annotation changed device terminals')
  same_nets!(pw_top_name, name, pw_top_name, name)
end
pw_audit['stages']['bound_layout_ports'] = pw_ports.call(pw_layout_top)
pw_save.call

# Invoked after the unchanged deck's normal preparation, before native comparison.
pw_verify_prepared = lambda do
  pw_reference_ports.call('after_simplify')
  layout_rows = pw_ports.call(netlist.circuit_by_name(pw_top_name))
  pw_audit['stages']['prepared_layout_ports'] = layout_rows
  pw_require.call(layout_rows.map { |r| r['name'] } == pw_spec['ports'], 'Prepared layout port identity/order changed')
  layout_rows.each do |row|
    pw_require.call(row['net'] == row['name'] && row['device_terminals'] > 0,
                    "Prepared layout port disconnected or misbound: #{row['name']}")
  end
  [['layout', netlist], ['schematic', schematic]].each do |label, target|
    state = pw_expanded.call(target.circuit_by_name(pw_top_name), [])
    pw_require.call(state['resistors'] == pw_flat[label]['resistors'],
                    "Simplification changed #{label} resistor inventory/dimensions")
    pw_audit['stages'][label + '_prepared'] = state
  end
  pw_audit['status'] = 'prepared'
  pw_save.call
end

# Invoked after native comparison and its existing empty-netlist/port guards.
pw_finish = lambda do |native_success|
  pw_audit['native_success'] = native_success
  pw_audit['status'] = native_success ? 'matched' : 'no_match'
  pw_save.call
end
