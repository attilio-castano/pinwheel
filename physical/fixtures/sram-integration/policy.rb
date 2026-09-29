# Diagnostic macro integration: no extraction/connectivity rule changes.
require 'json'
pw_contract = JSON.parse(File.read(ENV.fetch('PINWHEEL_POLICY_CONTRACT')))
pw_report = ENV.fetch('PINWHEEL_POLICY_REPORT')
pw_top = pw_contract.fetch('top')
pw_ref = pw_contract.fetch('reference_top')
pw_audit = {'policy' => pw_contract.fetch('policy'), 'status' => 'running',
            'top' => src.cell_name, 'stages' => {}, 'qualification' => false}
pw_save = lambda { File.write(pw_report, JSON.pretty_generate(pw_audit) + "\n") }
pw_require = lambda do |ok, message|
  unless ok
    pw_audit.merge!('status' => 'rejected', 'reason' => message)
    pw_save.call
    raise "PINWHEEL_POLICY_REJECT: #{message}"
  end
end
pw_require.call(src.cell_name == pw_top && $run_mode == 'deep', 'Unsupported input/mode')
pw_require.call(!NET_ONLY && !IGNORE_TOP_PORTS_MISMATCH && !PURGE && !PURGE_NETS && !TOP_LVL_PINS,
                'Unexpected netlist or port options')
pw_ports = lambda do |c|
  pw_require.call(!c.nil?, 'Missing macro top')
  c.each_pin.map do |p|
    n = c.net_for_pin(p.id)
    {'id' => p.id, 'name' => p.name, 'net' => n.nil? ? nil : n.name,
     'cluster' => n.nil? ? nil : n.cluster_id,
     'terminals' => n.nil? ? 0 : n.terminal_count,
     'child_pins' => n.nil? ? 0 : n.subcircuit_pin_count}
  end
end
pw_reference_ports = lambda do
  rows = pw_ports.call(schematic.circuit_by_name(pw_ref))
  pw_require.call(rows.map { |p| p['name'] } == pw_contract['ports'], 'Declared macro ports changed')
  pw_require.call(rows.all? { |p| p['terminals'] + p['child_pins'] > 0 }, 'Disconnected declared macro port')
  rows
end
# Memoized expansion counts every placement without flattening any circuit.
pw_state = lambda do |nl, top|
  memo = {}
  visit = nil
  visit = lambda do |c, stack|
    pw_require.call(!stack.include?(c.name), 'Recursive hierarchy')
    next memo[c.name] if memo.key?(c.name)
    models = Hash.new(0); dimensions = Hash.new(0); instances = Hash.new(0)
    c.each_device do |d|
      model = d.device_class.name.downcase
      models[model] += 1
      params = d.device_class.parameter_definitions.map { |p| [p.name, d.parameter(p.id)] }
      dimensions[JSON.generate([model, params])] += 1
    end
    c.each_subcircuit do |inst|
      child = inst.circuit_ref
      instances[child.name] += 1
      part = visit.call(child, stack + [c.name])
      part['models'].each { |k, v| models[k] += v }
      part['dimensions'].each { |k, v| dimensions[k] += v }
      part['instances'].each { |k, v| instances[k] += v }
    end
    memo[c.name] = {'models' => models.sort.to_h, 'dimensions' => dimensions.sort.to_h,
                    'instances' => instances.sort.to_h}
  end
  visit.call(nl.circuit_by_name(top), [])
end
pw_sides = [['layout', netlist, pw_top], ['schematic', schematic, pw_ref]]
pw_baseline = {}
pw_sides.each do |side, nl, top|
  pw_baseline[side] = pw_state.call(nl, top)
  nl.each_device_class do |dc|
    model = dc.name.downcase
    # Preserve all resistors for diagnosis. Only metal1 has qualified semantics.
    if model.start_with?('res_') || model == 'lvsres'
      dc.supports_serial_combination = false
      dc.supports_parallel_combination = false
    end
    if model == 'res_metal1'
      dc.enable_parameter('W', true); dc.enable_parameter('L', true)
      dc.enable_parameter('R', false)
    end
  end
end
pw_audit['unqualified_models'] = pw_baseline.transform_values do |state|
  state['models'].reject { |model, count| pw_contract['qualified_models'].include?(model) }
end
pw_audit['stages']['before_preparation'] = {
  'inventory' => pw_baseline, 'reference_ports' => pw_reference_ports.call}

# Macro labels may repeat, but every occurrence must probe the same physical net.
pw_source = RBA::Layout.new
pw_source.read($input)
pw_cell = pw_source.cell(pw_top)
pw_layout_top = netlist.circuit_by_name(pw_top)
pw_require.call(!pw_cell.nil? && !pw_layout_top.nil?, 'Missing physical macro')
pw_require.call(pw_layout_top.each_pin.to_a.empty?, 'Unexpected pre-existing macro pins')
pw_regions = {'10/25' => metal2_con.data, '50/25' => metal4_con.data}
pw_witnesses = []
pw_source.layer_indexes.each do |index|
  info = pw_source.get_info(index); layer = "#{info.layer}/#{info.datatype}"
  next unless pw_regions.key?(layer)
  pw_cell.shapes(index).each do |shape|
    next unless shape.is_text?
    label = shape.text
    pw_witnesses << {'name' => label.string, 'layer' => layer,
                    'x_um' => label.x * pw_source.dbu, 'y_um' => label.y * pw_source.dbu}
  end
end
pw_audit['physical_port_witnesses'] = pw_witnesses
pw_require.call(pw_witnesses.group_by { |w| w['layer'] }.transform_values(&:size) == pw_contract['boundary_layer_label_counts'], 'Physical label count changed')
pw_require.call(pw_witnesses.map { |w| w['name'] }.uniq.sort == pw_contract['ports'].sort, 'Physical macro port names changed')
pw_bindings = {}; pw_key = lambda { |n| [n.circuit.name, n.cluster_id] }
pw_witnesses.each do |w|
  path = []
  n = l2n_data.probe_net(pw_regions[w['layer']], RBA::DPoint.new(w['x_um'], w['y_um']), path, pw_layout_top)
  pw_require.call(!n.nil? && n.circuit.name == pw_top && path.empty?, "Label does not probe macro net: #{w['name']}")
  pw_require.call(n.cluster_id > 0 && n.terminal_count + n.subcircuit_pin_count > 0, "Disconnected physical macro port: #{w['name']}")
  if pw_bindings.key?(w['name'])
    pw_require.call(pw_key.call(pw_bindings[w['name']]) == pw_key.call(n), "Repeated port label probes distinct nets: #{w['name']}")
  else
    pw_require.call(!pw_bindings.values.any? { |prior| pw_key.call(prior) == pw_key.call(n) }, 'Different macro ports probe one net')
    pw_bindings[w['name']] = n
  end
  w['cluster_id'] = n.cluster_id; w['extracted_name'] = n.name
end
pw_audit['stages']['physical_bindings'] = {'ports' => pw_bindings.size, 'labels' => pw_witnesses.size}

# These operations expand only the two admitted families, retaining every device.
pw_sides.each do |side, nl, top|
  pw_contract['flatten_types'][side].each do |name|
    c = nl.circuit_by_name(name)
    pw_require.call(!c.nil?, "Missing scoped flatten target: #{name}")
    nl.flatten_circuit(c)
  end
  after = pw_state.call(nl, top)
  pw_require.call(after['models'] == pw_baseline[side]['models'] && after['dimensions'] == pw_baseline[side]['dimensions'], "Scoped flatten changed #{side} devices/parameters")
  pw_audit['stages'][side + '_scoped_flatten'] = after
end
pw_contract['pairs'].each do |layout_name, reference_name|
  pw_require.call(!netlist.circuit_by_name(layout_name).nil? && !schematic.circuit_by_name(reference_name).nil?, 'Missing explicit circuit pair')
  same_circuits(layout_name, reference_name)
end
pw_audit['circuit_pairs'] = pw_contract['pairs']
pw_contract['ports'].each do |name|
  n = pw_bindings.fetch(name)
  pw_require.call(!n._destroyed? && n.circuit.name == pw_top && n.terminal_count + n.subcircuit_pin_count > 0, "Scoped flatten lost port #{name}")
  other = pw_layout_top.net_by_name(name)
  pw_require.call(other.nil? || pw_key.call(other) == pw_key.call(n), "Physical name collision #{name}")
  count = n.terminal_count; n.name = name
  pin = pw_layout_top.create_pin(name); pw_layout_top.connect_pin(pin.id, n)
  pw_require.call(n.terminal_count == count, 'Port annotation changed terminals')
  same_nets!(pw_top, name, pw_ref, name)
end
pw_audit['stages']['bound_ports'] = pw_ports.call(pw_layout_top)
pw_save.call

pw_check = lambda do |stage, before_combine|
  result = {'reference_ports' => pw_reference_ports.call}
  rows = pw_ports.call(netlist.circuit_by_name(pw_top))
  pw_require.call(rows.map { |p| p['name'] } == pw_contract['ports'], "#{stage}: layout port identity changed")
  rows.each do |p|
    pw_require.call(p['net'] == p['name'] && p['cluster'] == pw_bindings[p['name']].cluster_id && p['terminals'] + p['child_pins'] > 0, "#{stage}: physical port binding lost")
  end
  result['layout_ports'] = rows
  pw_sides.each do |side, nl, top|
    state = pw_state.call(nl, top)
    pw_contract['preserved_array_types'][side].each do |name|
      pw_require.call(!nl.circuit_by_name(name).nil? && state['instances'][name] == pw_baseline[side]['instances'][name], "#{stage}: array hierarchy changed at #{name}")
    end
    if before_combine
      pw_require.call(state['models'] == pw_baseline[side]['models'] && state['dimensions'] == pw_baseline[side]['dimensions'], "#{stage}: devices/parameters changed")
    else
      old_res = pw_baseline[side]['dimensions'].select { |key, count| JSON.parse(key)[0].include?('res') }
      new_res = state['dimensions'].select { |key, count| JSON.parse(key)[0].include?('res') }
      pw_require.call(old_res == new_res, "#{stage}: resistor inventory/parameters changed")
    end
    result[side + '_inventory'] = state
  end
  pw_audit['stages'][stage] = result
  pw_save.call
end
pw_after_align = lambda { pw_check.call('after_alignment', true) }
pw_verify_prepared = lambda { pw_check.call('after_preparation', false) }
pw_finish = lambda do |success|
  pw_check.call('after_comparison', false)
  pw_audit['native_success'] = success
  pw_audit['status'] = success ? 'native_match' : 'native_no_match'
  pw_audit['qualification'] = success && pw_audit['unqualified_models'].values.all?(&:empty?)
  pw_save.call
end
