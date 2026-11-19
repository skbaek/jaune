import Jaune.Bridge.G2b.CheckedFrame
import Jaune.MessageCall.CheckedExec
import Jaune.MessageCall.FinalExec

/-! Forgetful observations of one step, an entering frame and a resumed caller. -/

namespace Jaune.Checked

variable [LegacyTransaction]

def Step.toLegacy : Step → Staging.Step
  | .exit e => .exit e.toLegacy
  | .next pc s => .next pc s.toLegacy
  | .spawn child p pc => .spawn child.toLegacy p pc

def Frame.Entry.toLegacy : Frame.Entry → Staging.Frame.Entry
  | .done x => .done x
  | .run r => .run r.toLegacy

def ResumeResult.toLegacy : Except (ExceptionalHalt × Frame.State) Frame.State →
    Except (ExceptionalHalt × Jaune.Frame.State) Jaune.Frame.State
  | .ok s => .ok s.toLegacy
  | .error (h,s) => .error (h,s.toLegacy)

end Jaune.Checked
