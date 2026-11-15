import Lean

namespace Jaune

structure Account where
  balance : Nat
  gasLimit : Nat

inductive Result where
  | success
  | failed

def sload : Nat := 0

end Jaune

namespace JauneConsensus

structure Context where
  eth1_data : Nat

end JauneConsensus
