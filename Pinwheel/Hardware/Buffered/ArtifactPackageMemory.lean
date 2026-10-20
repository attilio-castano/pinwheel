import Pinwheel.Hardware.Buffered.ArtifactPackageWiring

/-! Complete public interface and macro-instance inventory of the stateless
two-copy memory wrapper. Macro signal selections/constants are checked by the
package wiring certificate; the exact memory implementation still supplies its
explicit single-port digital law, rather than an electrical SRAM conclusion. -/
namespace Pinwheel.Hardware.Buffered.ArtifactPackageMemory
open ArtifactPackageWiring

structure Inventory where
  name : String
  interface : List Port
  instances : List (String × String)

def interface : List Port :=
  [⟨"clk",1,true⟩,⟨"mem_addr0",6,true⟩,⟨"mem_addr1",6,true⟩,
    ⟨"mem_data",64,true⟩,⟨"mem_write",1,true⟩,⟨"mem_read",1,true⟩,
    ⟨"mem_q0",64,false⟩,⟨"mem_q1",64,false⟩]

def canonical : Inventory :=
  ⟨"pinwheel_buffered_sram_memory", interface,
    [("storage0","RM_IHPSG13_1P_64x64_c2_bm_bist"),
      ("storage1","RM_IHPSG13_1P_64x64_c2_bm_bist")]⟩

structure Certificate (inventory : Inventory) : Prop where
  name : inventory.name = canonical.name
  interface : inventory.interface = canonical.interface
  instances : inventory.instances = canonical.instances

end Pinwheel.Hardware.Buffered.ArtifactPackageMemory
