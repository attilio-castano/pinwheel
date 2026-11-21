"""Conventional SystemVerilog implementation of the host transfer contract.

This generator uses ordinary arrays, request enables and a three-phase FSM.
It does not inspect Lean expressions, generated RTL, or oracle transitions.
"""
from __future__ import annotations

import re


def generate(a, wi, wo, module):
    if any(type(x) is not int or x <= 0 for x in (a, wi, wo)):
        raise ValueError("Positive integer physical widths required")
    if not isinstance(module, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", module):
        raise ValueError("Invalid module identifier")
    return f"""// Independent host transfer baseline: arrays, enables, and a three-phase FSM.
module {module} (
  input wire clk, reset, start_valid,
  input wire [{a-1}:0] source_base, destination_base,
  input wire [{a}:0] length,
  input wire source_req_valid, source_req_write,
  input wire [{a-1}:0] source_req_address,
  input wire [{wi-1}:0] source_req_data,
  input wire source_resp_ready,
  input wire destination_req_valid, destination_req_write,
  input wire [{a-1}:0] destination_req_address,
  input wire [{wo-1}:0] destination_req_data,
  input wire destination_resp_ready,
  output wire start_ready, busy, done, error,
  output wire source_req_ready, source_resp_valid,
  output wire [{wi-1}:0] source_resp_data,
  output wire destination_req_ready, destination_resp_valid,
  output wire [{wo-1}:0] destination_resp_data
);
  localparam integer DEPTH = {1 << a};
  reg [{wi-1}:0] source_words [0:DEPTH-1];
  reg [{wo-1}:0] destination_words [0:DEPTH-1];
  reg [{wi-1}:0] source_q;
  reg [{wo-1}:0] destination_q;
  reg source_pending, destination_pending;
  reg [1:0] phase;
  reg [{a-1}:0] latched_source_base, latched_destination_base;
  reg [{a}:0] transfer_length, completed;
  reg status_done, status_error;

  wire idle = phase == 2'd0;
  wire recovery = reset | (phase == 2'd3);
  // Widen before comparison: the capacity bit represents a full-depth job.
  wire [{a}:0] source_remaining = {a+1}'d{1 << a} - {{1'b0, source_base}};
  wire [{a}:0] destination_remaining = {a+1}'d{1 << a} - {{1'b0, destination_base}};
  wire fits = length <= source_remaining && length <= destination_remaining;
  wire [{a}:0] next_completed = completed + {a+1}'d1;
  wire [{a-1}:0] source_index = latched_source_base + completed;
  wire [{a-1}:0] destination_index = latched_destination_base + completed;
  // Invert at the source width; assignment then zero-extends or truncates.
  wire [{wi-1}:0] inverted_source = ~source_q;
  wire [{wo-1}:0] mapped_source = inverted_source;

  assign start_ready = !reset && idle && !source_pending && !destination_pending;
  assign busy = !recovery && !idle;
  assign done = !recovery && status_done;
  assign error = !recovery && status_error;
  assign source_req_ready = !recovery && idle && !start_valid && (!source_pending || source_resp_ready);
  assign source_resp_valid = !recovery && idle && source_pending;
  assign source_resp_data = source_resp_valid ? source_q : {wi}'d0;
  assign destination_req_ready = !recovery && idle && !start_valid && (!destination_pending || destination_resp_ready);
  assign destination_resp_valid = !recovery && idle && destination_pending;
  assign destination_resp_data = destination_resp_valid ? destination_q : {wo}'d0;

  always @(posedge clk) begin
    if (recovery) begin
      phase <= 2'd0;
      latched_source_base <= 0;
      latched_destination_base <= 0;
      transfer_length <= 0;
      completed <= 0;
      status_done <= 0;
      status_error <= !reset;
      source_pending <= 0;
      destination_pending <= 0;
      // Reset cancels protocol work. Arrays and Q intentionally retain data.
    end else begin
      status_done <= 0;
      status_error <= 0;
      case (phase)
        2'd0: begin
          if (start_valid && start_ready) begin
            completed <= 0;
            if (fits) begin
              latched_source_base <= source_base;
              latched_destination_base <= destination_base;
              transfer_length <= length;
              phase <= length == 0 ? 2'd0 : 2'd1;
              status_done <= length == 0;
            end else begin
              latched_source_base <= 0;
              latched_destination_base <= 0;
              transfer_length <= 0;
              phase <= 0;
              status_error <= 1;
            end
          end else begin
            // An offered start blocks new host requests, but responses drain.
            if (!source_pending || source_resp_ready) begin
              source_pending <= 0;
              if (source_req_valid && !start_valid) begin
                if (source_req_write)
                  source_words[source_req_address] <= source_req_data;
                else begin
                  source_q <= source_words[source_req_address];
                  source_pending <= 1;
                end
              end
            end
            if (!destination_pending || destination_resp_ready) begin
              destination_pending <= 0;
              if (destination_req_valid && !start_valid) begin
                if (destination_req_write)
                  destination_words[destination_req_address] <= destination_req_data;
                else begin
                  destination_q <= destination_words[destination_req_address];
                  destination_pending <= 1;
                end
              end
            end
          end
        end
        2'd1: begin
          destination_pending <= 0;
          if (!source_pending) begin
            source_q <= source_words[source_index];
            source_pending <= 1;
            phase <= 2'd2;
          end
        end
        2'd2: begin
          source_pending <= 0;
          destination_pending <= 0;
          if (source_pending) begin
            destination_words[destination_index] <= mapped_source;
            completed <= next_completed;
            if (next_completed < transfer_length)
              phase <= 2'd1;
            else begin
              phase <= 2'd0;
              status_done <= 1;
            end
          end
        end
        default: phase <= 2'd0;
      endcase
    end
  end
endmodule
"""


def register_references(a):
    return ["phase", "latched_source_base", "latched_destination_base", "transfer_length",
            "completed", "status_done", "status_error"] + [f"source_words[{i}]" for i in range(1 << a)] + [
                "source_q", "source_pending"] + [f"destination_words[{i}]" for i in range(1 << a)] + [
                "destination_q", "destination_pending"]


def mutations(text, wi, wo):
    marker = "      // Reset cancels protocol work. Arrays and Q intentionally retain data."
    if text.count(marker) != 1:
        raise ValueError("Missing unique reset body")
    yield "reset-clears-word", text.replace(marker, f"      destination_words[0] <= {wo}'d0;\n"+marker)
    marker = "      case (phase)"
    if text.count(marker) != 1:
        raise ValueError("Missing unique controller body")
    yield "busy-host-write", text.replace(marker,
        "      if (busy && source_req_valid && source_req_write) source_words[0] <= source_req_data;\n"+marker)
    marker = "mapped_source = inverted_source;"
    if text.count(marker) != 1:
        raise ValueError("Missing unique transform")
    yield "omit-inversion", text.replace(marker, "mapped_source = source_q;")
