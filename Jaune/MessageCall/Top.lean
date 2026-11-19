import Jaune.MessageCall.Exec

/-!
# The top-level frame

A top-level message call runs one frame whose checkpoint is the state its message was prepared
on: `initDevm` of the message, or under Amsterdam's rules the state `prepareTopLevelAmsterdam`
returns. `Frame.runTop` enters it from that checkpoint, runs `exec` and settles. The transaction
reads the settled `Frame.Result` through `Frame.output` and `Frame.outputAmsterdam`.

`Msg` is the top-level message type, and `Message.ofTop` builds the frame's message from it.
-/

namespace Jaune

open Jaune

/-- A top-level `Msg` as a frame message. `isCreate` gives the kind; it is the frame's flag,
not the message's. -/
def Message.ofTop (msg : Msg) (isCreate : Bool) : Message :=
  { context :=
      { caller := msg.caller, recipient := msg.currentTarget, value := msg.value
        calldata := msg.data, code := msg.code, depthLeft := msg.depth
        isStatic := msg.isStatic, tx := msg.tenv.stat, block := msg.benv.stat }
    kind := if isCreate then .create else .call
    codeAddress := msg.codeAddress
    target := msg.target
    gas := msg.gas
    stateGasGrant := msg.stateGasGrant
    transfersValue := msg.shouldTransferValue
    disablePrecompiles := msg.disablePrecompiles }

/-- A top-level frame: the checkpoint is the state its message starts on. -/
def Frame.ofTop (msg : Msg) (isCreate : Bool) : Frame :=
  ⟨Message.ofTop msg isCreate, Frame.State.ofDevm (initDevm msg)⟩

/-- Run a top-level frame: enter it from its checkpoint, run the code, settle. -/
def Frame.runTop (f : Frame) : Except Fault Frame.Result :=
  match enterWith f f.checkpoint.toDevm with
  | .done result => result
  | .run evm => settle f (exec evm)




end Jaune
