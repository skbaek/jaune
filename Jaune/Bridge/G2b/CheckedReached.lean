import Jaune.Bridge.G2b.CheckedReachInduction
import Jaune.Bridge.G2b.CheckedStep

namespace Jaune.Evm.Reaches

/-- Every running machine reached from a well-formed start has well-formed memory. -/
theorem memory_wf {start evm : Evm} (h : start.Reaches evm) (hw : start.dyna.memory.Wf) :
    evm.dyna.memory.Wf := MemoryReachability.reaches_memory_wf_of_step MemorySimulation.step hw h

/-- A spawned frame saves exactly the caller checkpoint whose memory this fact covers. -/
theorem checkpoint_memory_wf {start evm : Evm} (h : start.Reaches evm) (hw : start.dyna.memory.Wf)
    {child : Frame} {p : Pending} {pc : Nat} (hs : Evm.step evm = .spawn child p pc) :
    child.checkpoint.machine.memory.Wf := MemoryReachability.checkpoint_memory_wf_of_step MemorySimulation.step hw h hs

end Jaune.Evm.Reaches
