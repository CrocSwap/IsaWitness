import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0036
import ArmFull.Fn.M0144
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0181
import ArmFull.Fn.M0194
import ArmFull.Fn.M0215
import ArmFull.Fn.M0226
import ArmFull.Fn.M0227

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace ArmFull

variable {real : Type} [Sail.SailReal real]

open ConcurrencyInterfaceV1

namespace Functions

open signal
open option
open exception
open arm_acc_type
open __InstrEnc
open WFxType
open VFPNegMul
open VCGTtype
open VCGEType
open VBitOps
open VBitOp
open VARange
open Unpredictable
open TranslationStage
open TimeStamp
open TMFailure
open TLBIOp
open TLBIMemAttr
open TLBILevel
open TGx
open SystemHintOp
open Signal
open ShiftType
open Shareability
open SecurityState
open SVECmp
open SRType
open SMEExceptionType
open SDFType
open RestrictType
open Register
open Regime
open ReduceOp
open PrivilegeLevel
open PrefetchHint
open PSTATEField
open PGSe
open PASpace
open PARTIDspaceType
open OpType
open MoveWideOp
open MemType
open MemTagType
open MemOp
open MemAtomicOp
open MOPSStage
open MBReqTypes
open MBReqDomain
open LogicalOp
open InterruptID
open InstrSet
open ImmediateOp
open GPCF
open GCSInstruction
open Feature
open Fault
open FPUnaryOp
open FPType
open FPRounding
open FPMaxMinOp
open FPExc
open FPConvOp
open ExtendType
open ExceptionalOccurrenceTargetState
open Exception
open ErrorState
open DeviceType
open DescriptorType
open DSBAlias
open CrossTriggerIn
open CountOp
open Constraint
open CompareOp
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open BranchType
open BarrierExt
open Barrier
open ArchVersion
open AccessType
open ATAccess

/-- Type quantifiers: k_trappedsyscallinst : Bool -/
def BRBEException (erec : ExceptionRecord) (preferred_exception_return : (BitVec 64)) (target_address_in : (BitVec 64)) (target_el : (BitVec 2)) (trappedsyscallinst : Bool) : SailM Unit := SailME.run do
  let target_address : (BitVec 64) := target_address_in
  let except : Exception := erec.exceptype
  let iss : (BitVec 25) := erec.syndrome
  let questionMark := target_el
  if ((questionMark == EL3) : Bool)
  then
    (do
      let w__3 ← (( do
        if ((← do
             let w__0 ← (( do (HaveBRBEv1p1 ()) ) : SailME Unit Bool )
             (pure (((! w__0) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__1 ← (( do readReg MDCR_EL3 ) : SailME Unit (BitVec 64) )
            let w__2 ← (( do readReg MDCR_EL3 ) : SailME Unit (BitVec 64) )
            (pure ((((_get_MDCR_EL3_Type_E3BREC w__1) == (_get_MDCR_EL3_Type_E3BREW w__2)) : Bool))))
        ) : SailME Unit Bool )
      if (w__3 : Bool)
      then
        (do
          SailME.throw (() : Unit))
      else (pure (())))
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          let w__4 ← (( do readReg BRBCR_EL2 ) : SailME Unit (BitVec 64) )
          if (((_get_BRBCR_EL2_Type_EXCEPTION w__4) == 0#1) : Bool)
          then
            (do
              SailME.throw (() : Unit))
          else (pure (())))
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              let w__5 ← (( do readReg BRBCR_EL1 ) : SailME Unit (BitVec 64) )
              if (((_get_BRBCR_EL1_Type_EXCEPTION w__5) == 0#1) : Bool)
              then
                (do
                  SailME.throw (() : Unit))
              else (pure (())))
          else (pure (()))))
  let w__6 ← (( do readReg PSTATE ) : SailME Unit ProcState )
  let source_valid ← (( do (BranchRecordAllowed w__6.EL) ) : SailME Unit Bool )
  let target_valid ← (( do (BranchRecordAllowed target_el) ) : SailME Unit Bool )
  let branch_valid : Bool := (source_valid || target_valid)
  if (branch_valid : Bool)
  then
    (do
      let branch_type ← (( do (undefined_bitvector_at (← occLabel 695) 6) ) : SailME Unit
        (BitVec 6) )
      let branch_type ← (( do
        match except with
        | .Exception_Uncategorized => (pure (0b100011#6))
        | .Exception_WFxTrap => (pure (0b100011#6))
        | .Exception_CP15RTTrap => (pure (0b100011#6))
        | .Exception_CP15RRTTrap => (pure (0b100011#6))
        | .Exception_CP14RTTrap => (pure (0b100011#6))
        | .Exception_CP14DTTrap => (pure (0b100011#6))
        | .Exception_AdvSIMDFPAccessTrap => (pure (0b100011#6))
        | .Exception_FPIDTrap => (pure (0b100011#6))
        | .Exception_PACTrap => (pure (0b100011#6))
        | .Exception_TSTARTAccessTrap => (pure (0b100011#6))
        | .Exception_CP14RRTTrap => (pure (0b100011#6))
        | .Exception_BranchTarget => (pure (0b101011#6))
        | .Exception_IllegalState => (pure (0b100011#6))
        | .Exception_SupervisorCall =>
          (let branch_type : (BitVec 6) :=
            if ((! trappedsyscallinst) : Bool)
            then 0b100010#6
            else 0b100011#6
          (pure (branch_type)))
        | .Exception_HypervisorCall => (pure (0b100010#6))
        | .Exception_MonitorCall =>
          (let branch_type : (BitVec 6) :=
            if ((! trappedsyscallinst) : Bool)
            then 0b100010#6
            else 0b100011#6
          (pure (branch_type)))
        | .Exception_SystemRegisterTrap => (pure (0b100011#6))
        | .Exception_SystemRegister128Trap => (pure (0b100011#6))
        | .Exception_SVEAccessTrap => (pure (0b100011#6))
        | .Exception_SMEAccessTrap => (pure (0b100011#6))
        | .Exception_ERetTrap => (pure (0b100011#6))
        | .Exception_PACFail => (pure (0b101100#6))
        | .Exception_InstructionAbort => (pure (0b101011#6))
        | .Exception_PCAlignment => (pure (0b101010#6))
        | .Exception_DataAbort => (pure (0b101100#6))
        | .Exception_NV2DataAbort => (pure (0b101100#6))
        | .Exception_SPAlignment => (pure (0b101010#6))
        | .Exception_FPTrappedException => (pure (0b100011#6))
        | .Exception_SError => (pure (0b100100#6))
        | .Exception_Breakpoint => (pure (0b100110#6))
        | .Exception_SoftwareStep => (pure (0b100110#6))
        | .Exception_Watchpoint => (pure (0b100111#6))
        | .Exception_NV2Watchpoint => (pure (0b100111#6))
        | .Exception_SoftwareBreakpoint => (pure (0b100110#6))
        | .Exception_IRQ => (pure (0b101110#6))
        | .Exception_FIQ => (pure (0b101111#6))
        | .Exception_MemCpyMemSet => (pure (0b100011#6))
        | .Exception_GCSFail =>
          (do
            if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb iss 23 20)) == 0b0000#4) : Bool)
            then (pure (0b101100#6))
            else
              (do
                if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb iss 23 20)) == 0b0001#4) : Bool)
                then (pure (0b101011#6))
                else
                  (do
                    if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb iss 23 20)) == 0b0010#4) : Bool)
                    then (pure (0b100011#6))
                    else
                      (do
                        (Unreachable ())
                        (pure (branch_type))))))
        | _ =>
          (do
            (Unreachable ())
            (pure (branch_type))) ) : SailME Unit (BitVec 6) )
      let ccu ← (( do (undefined_bitvector_at (← occLabel 696) 1) ) : SailME Unit (BitVec 1) )
      let cc ← (( do (undefined_bitvector_at (← occLabel 697) 14) ) : SailME Unit (BitVec 14) )
      let w__7 ← (( do (BranchEncCycleCount ()) ) : SailME Unit ((BitVec 1) × (BitVec 14)) )
      let (tup__0, tup__1) := (w__7 : ((BitVec 1) × (BitVec 14)))
      let ccu : (BitVec 1) := tup__0
      let cc : (BitVec 14) := tup__1
      let w__8 ← (( do (HaveTME ()) ) : SailME Unit Bool )
      let lastfailed ← (( do
        if (w__8 : Bool)
        then
          (do
            let w__9 ← (( do readReg BRBFCR_EL1 ) : SailME Unit (BitVec 64) )
            (pure ((_get_BRBFCR_EL1_Type_LASTFAILED w__9))))
        else (pure (0#1)) ) : SailME Unit (BitVec 1) )
      let w__13 ← (( do
        if ((← if (source_valid : Bool)
             then
               (do
                 (HaveTME ()))
             else (pure false)) : Bool)
        then
          (do
            let w__12 ← (( do readReg TSTATE ) : SailME Unit TMState )
            (pure (((w__12.depth >b 0) : Bool))))
        else (pure false) ) : SailME Unit Bool )
      let transactional : (BitVec 1) :=
        if (w__13 : Bool)
        then 1#1
        else 0#1
      let el : (BitVec 2) :=
        if (target_valid : Bool)
        then target_el
        else 0b00#2
      let mispredict : (BitVec 1) := 0#1
      let sv : (BitVec 1) :=
        if (source_valid : Bool)
        then 1#1
        else 0#1
      let tv : (BitVec 1) :=
        if (target_valid : Bool)
        then 1#1
        else 0#1
      let source_address : (BitVec 64) :=
        if (source_valid : Bool)
        then preferred_exception_return
        else (Zeros (n := 64))
      let target_address ← (( do
        if ((! target_valid) : Bool)
        then
          (let target_address : (BitVec 64) := (Zeros (n := 64))
          (pure (target_address)))
        else
          (do
            (AArch64_BranchAddr target_address target_el)) ) : SailME Unit (BitVec 64) )
      (UpdateBranchRecordBuffer ccu cc lastfailed transactional branch_type el mispredict
        (sv +++ tv) source_address target_address)
      let w__15 ← (( do readReg BRBFCR_EL1 ) : SailME Unit (BitVec 64) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__15 6 6 0#1)
      (PMUEvent PMU_EVENT_BRB_FILTRATE))
  else (pure (()))
  writeReg __last_branch_valid branch_valid


/-- Type quantifiers: k_iesb_req : Bool -/
def TakeUnmaskedPhysicalSErrorInterrupts (iesb_req : Bool) : SailM Unit := do
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let (AA, IRQ, FIQ) ← (( do (AArch32_PendingUnmaskedPhysicalInterrupts ()) ) : SailM
        (Bool × Bool × Bool) )
      if (AA : Bool)
      then
        (do
          (ThrowSError iesb_req))
      else (pure (())))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      let (SE, IRQ, FIQ) ← (( do
        (AArch64_PendingUnmaskedPhysicalInterrupts (w__1.A +++ (w__2.I +++ w__3.F))) ) : SailM
        (Bool × Bool × Bool) )
      if (SE : Bool)
      then
        (do
          (ThrowSError iesb_req))
      else (pure (())))


def CreateAccDescIFetch (_ : Unit) : SailM AccessDescriptor := do
  (NewAccDesc AccessType_IFETCH)


/-- Type quantifiers: k_nontemporal : Bool, k_privileged : Bool, k_tagchecked : Bool -/
def CreateAccDescGPR (memop : MemOp) (nontemporal : Bool) (privileged : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let w__1 ← (( do
    if ((! privileged) : Bool)
    then (pure (EL0))
    else
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (w__0.EL))) ) : SailM (BitVec 2) )
  let accdesc := ({ accdesc with el := w__1 } : AccessDescriptor)
  let accdesc : AccessDescriptor := { accdesc with nontemporal := nontemporal }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  let w__4 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__3 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__3.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__4 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_acqrel : Bool, k_tagchecked : Bool -/
def CreateAccDescExLDST (memop : MemOp) (acqrel : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqsc := (acqrel && (BEq.beq memop MemOp_LOAD)) }
  let accdesc : AccessDescriptor :=
    { accdesc with relsc := (acqrel && (BEq.beq memop MemOp_STORE)) }
  let accdesc : AccessDescriptor := { accdesc with exclusive := true }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__2 } : AccessDescriptor)
  (pure (accdesc))


def CreateAccDescLDGSTG (memop : MemOp) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagaccess := true }
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__2 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_nontemporal : Bool, k_privileged : Bool -/
def CreateAccDescMOPS (memop : MemOp) (privileged : Bool) (nontemporal : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let w__1 ← (( do
    if ((! privileged) : Bool)
    then (pure (EL0))
    else
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (w__0.EL))) ) : SailM (BitVec 2) )
  let accdesc := ({ accdesc with el := w__1 } : AccessDescriptor)
  let accdesc : AccessDescriptor := { accdesc with nontemporal := nontemporal }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with mops := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := true }
  let w__4 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__3 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__3.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__4 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_nontemporal : Bool, k_privileged : Bool -/
def CreateAccDescSTGMOPS (privileged : Bool) (nontemporal : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let w__1 ← (( do
    if ((! privileged) : Bool)
    then (pure (EL0))
    else
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (w__0.EL))) ) : SailM (BitVec 2) )
  let accdesc := ({ accdesc with el := w__1 } : AccessDescriptor)
  let accdesc : AccessDescriptor := { accdesc with nontemporal := nontemporal }
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with mops := true }
  let accdesc : AccessDescriptor := { accdesc with tagaccess := true }
  let w__4 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__3 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__3.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__4 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_acquire : Bool, k_release : Bool, k_tagchecked : Bool -/
def CreateAccDescAtomicOp (modop : MemAtomicOp) (acquire : Bool) (release : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqsc := acquire }
  let accdesc : AccessDescriptor := { accdesc with relsc := release }
  let accdesc : AccessDescriptor := { accdesc with atomicop := true }
  let accdesc : AccessDescriptor := { accdesc with modop := modop }
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__2 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_acquire : Bool, k_release : Bool, k_soft : Bool, k_tagchecked : Bool -/
def CreateAccDescRCW (modop : MemAtomicOp) (soft : Bool) (acquire : Bool) (release : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqsc := acquire }
  let accdesc : AccessDescriptor := { accdesc with relsc := release }
  let accdesc : AccessDescriptor := { accdesc with rcw := true }
  let accdesc : AccessDescriptor := { accdesc with rcws := soft }
  let accdesc : AccessDescriptor := { accdesc with atomicop := true }
  let accdesc : AccessDescriptor := { accdesc with modop := modop }
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__2 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_tagchecked : Bool -/
def CreateAccDescAcqRel (memop : MemOp) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqsc := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with relsc := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__2 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_tagchecked : Bool -/
def CreateAccDescLOR (memop : MemOp) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqsc := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with relsc := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with limitedordered := true }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__2 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_tagchecked : Bool -/
def CreateAccDescLDAcqPC (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqpc := true }
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__2 } : AccessDescriptor)
  (pure (accdesc))


def CreateAccDescA32LSMD (memop : MemOp) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with a32lsmd := true }
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__2 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_tagchecked : Bool -/
def CreateAccDescLS64 (memop : MemOp) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with ls64 := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__2 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_nontemporal : Bool, k_tagchecked : Bool -/
def CreateAccDescASIMD (memop : MemOp) (nontemporal : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_ASIMD) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with nontemporal := nontemporal }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let w__0 ← (( do (InStreamingMode ()) ) : SailM Bool )
  let accdesc := ({ accdesc with streamingsve := w__0 } : AccessDescriptor)
  let w__2 ← (( do
    if ((accdesc.streamingsve : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "No tag checking of SIMD&FP loads and stores in Streaming SVE mode"))
    else (pure false) ) : SailM Bool )
  let accdesc : AccessDescriptor :=
    if (w__2 : Bool)
    then { accdesc with tagchecked := false }
    else { accdesc with tagchecked := tagchecked }
  let w__5 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__4 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__4.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__5 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_tagchecked : Bool -/
def CreateAccDescASIMDAcqRel (memop : MemOp) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_ASIMD) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqpc := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with relsc := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let w__0 ← (( do (InStreamingMode ()) ) : SailM Bool )
  let accdesc := ({ accdesc with streamingsve := w__0 } : AccessDescriptor)
  let w__2 ← (( do
    if ((accdesc.streamingsve : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "No tag checking of SIMD&FP loads and stores in Streaming SVE mode"))
    else (pure false) ) : SailM Bool )
  let accdesc : AccessDescriptor :=
    if (w__2 : Bool)
    then { accdesc with tagchecked := false }
    else { accdesc with tagchecked := tagchecked }
  let w__5 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__4 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__4.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__5 } : AccessDescriptor)
  (pure (accdesc))


def CreateAccDescIC (cache : CacheRecord) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_IC) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with cacheop := cache.cacheop }
  let accdesc : AccessDescriptor := { accdesc with cachetype := cache.cachetype }
  let accdesc : AccessDescriptor := { accdesc with opscope := cache.opscope }
  (pure (accdesc))


def CreateAccDescDC (cache : CacheRecord) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_DC) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with cacheop := cache.cacheop }
  let accdesc : AccessDescriptor := { accdesc with cachetype := cache.cachetype }
  let accdesc : AccessDescriptor := { accdesc with opscope := cache.opscope }
  (pure (accdesc))


/-- Type quantifiers: k_tagaccess : Bool, k_tagchecked : Bool -/
def CreateAccDescDCZero (tagaccess : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_DCZero) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  let accdesc : AccessDescriptor := { accdesc with tagaccess := tagaccess }
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__2 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_pan : Bool, k_write : Bool -/
def CreateAccDescAT (ss : SecurityState) (el : (BitVec 2)) (write : Bool) (pan : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_AT) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := el }
  let accdesc : AccessDescriptor := { accdesc with ss := ss }
  let accdesc : AccessDescriptor := { accdesc with read := (! write) }
  let accdesc : AccessDescriptor := { accdesc with write := write }
  let accdesc : AccessDescriptor := { accdesc with pan := pan }
  (pure (accdesc))


def CreateAccDescTTEUpdate (accdesc_in : AccessDescriptor) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_TTW) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := accdesc_in.el }
  let accdesc : AccessDescriptor := { accdesc with ss := accdesc_in.ss }
  let accdesc : AccessDescriptor := { accdesc with atomicop := true }
  let accdesc : AccessDescriptor := { accdesc with modop := MemAtomicOp_CAS }
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with mpam := accdesc_in.mpam }
  (pure (accdesc))


/-- Type quantifiers: k_toplevel : Bool -/
def CreateAccDescS1TTW (toplevel : Bool) (varange : VARange) (accdesc_in : AccessDescriptor) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_TTW) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := accdesc_in.el }
  let accdesc : AccessDescriptor := { accdesc with ss := accdesc_in.ss }
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with toplevel := toplevel }
  let accdesc : AccessDescriptor := { accdesc with varange := varange }
  let accdesc : AccessDescriptor := { accdesc with mpam := accdesc_in.mpam }
  (pure (accdesc))


end ArmFull.Functions
