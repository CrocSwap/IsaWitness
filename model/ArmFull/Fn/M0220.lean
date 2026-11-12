import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0036
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0052
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0058
import ArmFull.Fn.M0059
import ArmFull.Fn.M0079
import ArmFull.Fn.M0080
import ArmFull.Fn.M0081
import ArmFull.Fn.M0082
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0140
import ArmFull.Fn.M0141
import ArmFull.Fn.M0144
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0184
import ArmFull.Fn.M0186
import ArmFull.Fn.M0189
import ArmFull.Fn.M0196
import ArmFull.Fn.M0197
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0204
import ArmFull.Fn.M0213

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

def AArch32_vESBOperation (_ : Unit) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL1) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:42806.63-42806.64"
  let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
  if ((! w__5) : Bool)
  then
    (do
      (AArch64_vESBOperation ()))
  else
    (do
      let vSEI_enabled ← (( do
        if ((← do
             let w__6 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
             (pure ((((_get_HCR_Type_TGE w__6) == 0#1) : Bool)))) : Bool)
        then
          (do
            let w__7 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_HCR_Type_AMO w__7) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      let vSEI_pending ← (( do
        if (vSEI_enabled : Bool)
        then
          (do
            let w__8 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_HCR_Type_VA w__8) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      let vintdis ← (( do
        if ((← do
             (Halted ())) : Bool)
        then (pure true)
        else
          (do
            (ExternalDebugInterruptsDisabled EL1)) ) : SailM Bool )
      let vmasked ← (( do
        if (vintdis : Bool)
        then (pure true)
        else
          (do
            let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__11.A == 1#1) : Bool)))) ) : SailM Bool )
      if ((vSEI_pending && vmasked) : Bool)
      then
        (do
          let syndrome : (BitVec 32) := (Zeros (n := 32))
          let syndrome : (BitVec 32) := (BitVec.update syndrome 31 (Bit 1#1))
          let w__12 ← (( do (VDFSR_read ()) ) : SailM (BitVec 32) )
          let syndrome :=
            ((Sail.BitVec.updateSubrange syndrome 15 14 (Sail.BitVec.extractLsb w__12 15 14)) : (BitVec 32))
          let w__13 ← (( do (VDFSR_read ()) ) : SailM (BitVec 32) )
          let syndrome :=
            ((BitVec.update syndrome 12
              (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__13 12)])))) : (BitVec 32))
          let w__14 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
          let syndrome :=
            ((BitVec.update syndrome 9 (Bit (_get_TTBCR_Type_EAE w__14))) : (BitVec 32))
          let w__15 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
          let syndrome : (BitVec 32) :=
            if (((_get_TTBCR_Type_EAE w__15) == 1#1) : Bool)
            then (Sail.BitVec.updateSubrange syndrome 5 0 0b010001#6)
            else
              (let syndrome : (BitVec 32) :=
                (Sail.BitVec.updateSubrange syndrome 10 10 (Sail.BitVec.extractLsb 0b10110#5 4 4))
              (Sail.BitVec.updateSubrange syndrome 3 0 (Sail.BitVec.extractLsb 0b10110#5 3 0)))
          (VDISR_write (Mk_VDISR_Type syndrome))
          let w__16 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
          (HCR_write (_update_HCR_Type_VA w__16 0#1)))
      else (pure (())))


def AArch32_CheckSETENDEnabled (_ : Unit) : SailM Unit := do
  let setend_disabled ← (( do (undefined_bitvector_at (← occLabel 2791) 1) ) : SailM (BitVec 1)
    )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let setend_disabled ← (( do
    if ((w__0.EL == EL2) : Bool)
    then
      (do
        let w__1 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
        let setend_disabled := ((_get_HSCTLR_Type_SED w__1) : (BitVec 1))
        (pure (setend_disabled)))
    else
      (do
        let w__2 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
            (pure ((_get_SCTLR_Type_SED w__3))))
        else
          (do
            let w__4 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
            (pure ((_get_SCTLRType_SED w__4))))) ) : SailM (BitVec 1) )
  if ((setend_disabled == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let setend_disabled := setend_disabled
  (pure (()))


def MAIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MAIR0_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (MAIR0_S_write r))
  else
    (do
      (MAIR0_NS_write r))


def MAIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MAIR1_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (MAIR1_S_write r))
  else
    (do
      (MAIR1_NS_write r))


def LR_read (_ : Unit) : SailM (BitVec 32) := do
  (R_read 14)


def AArch64_PendingUnmaskedVirtualInterrupts (mask_in : (BitVec 3)) : SailM (Bool × Bool × Bool) := do
  let allintmask ← (( do (undefined_bitvector_at (← occLabel 2868) 1) ) : SailM (BitVec 1) )
  let mask : (BitVec 3) := mask_in
  let pending ← (( do (undefined_bitvector_at (← occLabel 2869) 3) ) : SailM (BitVec 3) )
  let w__6 ← (( do
    if ((← do
         if ((← do
              if ((← do
                   let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__0.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__1.EL == EL1) : Bool))))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let (mask, pending) ← (( do
    if (w__6 : Bool)
    then
      (do
        let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__12 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let pending :=
          ((((_get_HCR_EL2_Type_VSE w__7) +++ ((_get_HCR_EL2_Type_VI w__8) +++ (_get_HCR_EL2_Type_VF
                  w__9))) &&& ((_get_HCR_EL2_Type_AMO w__10) +++ ((_get_HCR_EL2_Type_IMO w__11) +++ (_get_HCR_EL2_Type_FMO
                  w__12)))) : (BitVec 3))
        let w__15 ← (( do
          if ((← do
               (HaveFeatNMI ())) : Bool)
          then
            (do
              let w__14 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
              (pure ((((_get_SCTLRType_NMI w__14) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let mask ← (( do
          if (w__15 : Bool)
          then
            (do
              let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__18 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
              let allintmask : (BitVec 1) :=
                (w__16.ALLINT ||| (w__17.SP &&& (_get_SCTLRType_SPINTMASK w__18)))
              let w__22 ← (( do
                if ((← do
                     (IsHCRXEL2Enabled ())) : Bool)
                then
                  (do
                    (pure ((← do
                          let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__20.EL == EL0) : Bool)))) || ((allintmask == 0#1) : Bool))))
                else (pure false) ) : SailM Bool )
              let mask ← (( do
                if (w__22 : Bool)
                then
                  (do
                    let w__23 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                    let mask : (BitVec 3) :=
                      if (((_get_HCRX_EL2_Type_VFNMI w__23) == 1#1) : Bool)
                      then (BitVec.update mask 0 (Bit 0#1))
                      else mask
                    let w__24 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                    let mask : (BitVec 3) :=
                      if (((_get_HCRX_EL2_Type_VINMI w__24) == 1#1) : Bool)
                      then (BitVec.update mask 1 (Bit 0#1))
                      else mask
                    (pure (mask)))
                else (pure (mask)) ) : SailM (BitVec 3) )
              let w__26 ← (( do
                (pure ((← do
                      let w__25 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__25.EL == EL1) : Bool)))) && ((allintmask == 1#1) : Bool))) ) :
                SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let mask : (BitVec 3) :=
                    if (((_get_HCR_EL2_Type_FMO w__27) == 1#1) : Bool)
                    then (BitVec.update mask 0 (Bit 1#1))
                    else mask
                  let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let mask : (BitVec 3) :=
                    if (((_get_HCR_EL2_Type_IMO w__28) == 1#1) : Bool)
                    then (BitVec.update mask 1 (Bit 1#1))
                    else mask
                  (pure (mask)))
              else (pure (mask)))
          else (pure (mask)) ) : SailM (BitVec 3) )
        (pure ((mask, pending))))
    else
      (let pending : (BitVec 3) := 0b000#3
      (pure ((mask, pending)))) ) : SailM ((BitVec 3) × (BitVec 3)) )
  let unmasked_pending : (BitVec 3) := (pending &&& (Complement.complement mask))
  (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access unmasked_pending 2)])) == 1#1), ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          unmasked_pending 1)])) == 1#1), ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          unmasked_pending 0)])) == 1#1))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_06329c412b3ab5ff (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 1) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__3.EL) : Bool)
      then
        (do
          let w__4 ← (( do (R_read t2) ) : SailM (BitVec 32) )
          let w__5 ← (( do (R_read t) ) : SailM (BitVec 32) )
          (AMEVCNTR1_set 1 (Mk_AMEVCNTR1_Type (w__4 +++ w__5))))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_18488936f5130285 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 4) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__3.EL) : Bool)
      then
        (do
          let w__4 ← (( do (R_read t2) ) : SailM (BitVec 32) )
          let w__5 ← (( do (R_read t) ) : SailM (BitVec 32) )
          (AMEVCNTR1_set 4 (Mk_AMEVCNTR1_Type (w__4 +++ w__5))))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_4a0c18bf00eccda4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 2) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__3.EL) : Bool)
      then
        (do
          let w__4 ← (( do (R_read t2) ) : SailM (BitVec 32) )
          let w__5 ← (( do (R_read t) ) : SailM (BitVec 32) )
          (AMEVCNTR1_set 2 (Mk_AMEVCNTR1_Type (w__4 +++ w__5))))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_80489a0c42f5990f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 3) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__3.EL) : Bool)
      then
        (do
          let w__4 ← (( do (R_read t2) ) : SailM (BitVec 32) )
          let w__5 ← (( do (R_read t) ) : SailM (BitVec 32) )
          (AMEVCNTR1_set 3 (Mk_AMEVCNTR1_Type (w__4 +++ w__5))))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_8a065d943b8f719e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 0) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__3.EL) : Bool)
      then
        (do
          let w__4 ← (( do (R_read t2) ) : SailM (BitVec 32) )
          let w__5 ← (( do (R_read t) ) : SailM (BitVec 32) )
          (AMEVCNTR1_set 0 (Mk_AMEVCNTR1_Type (w__4 +++ w__5))))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_8ea485840df13e8b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 6) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__3.EL) : Bool)
      then
        (do
          let w__4 ← (( do (R_read t2) ) : SailM (BitVec 32) )
          let w__5 ← (( do (R_read t) ) : SailM (BitVec 32) )
          (AMEVCNTR1_set 6 (Mk_AMEVCNTR1_Type (w__4 +++ w__5))))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_9589f0d5bbc35480 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 5) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__3.EL) : Bool)
      then
        (do
          let w__4 ← (( do (R_read t2) ) : SailM (BitVec 32) )
          let w__5 ← (( do (R_read t) ) : SailM (BitVec 32) )
          (AMEVCNTR1_set 5 (Mk_AMEVCNTR1_Type (w__4 +++ w__5))))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_a0a98205a8cc86f4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 7) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__3.EL) : Bool)
      then
        (do
          let w__4 ← (( do (R_read t2) ) : SailM (BitVec 32) )
          let w__5 ← (( do (R_read t) ) : SailM (BitVec 32) )
          (AMEVCNTR1_set 7 (Mk_AMEVCNTR1_Type (w__4 +++ w__5))))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int, t2 : Int -/
def CNTHP_CVAL_SysRegWrite64_558ce8493f8ab75e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do (R_read t2) ) : SailM (BitVec 32) )
              let w__3 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (CNTHP_CVAL_write (Mk_CNTHP_CVAL_Type (w__2 +++ w__3))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__4 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__5 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (CNTHP_CVAL_write (Mk_CNTHP_CVAL_Type (w__4 +++ w__5)))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def CNTVOFF_SysRegWrite64_772809c07f941c73 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do (R_read t2) ) : SailM (BitVec 32) )
              let w__3 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (CNTVOFF_write (w__2 +++ w__3)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__4 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__5 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (CNTVOFF_write (w__4 +++ w__5))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHCTL_SysRegRead32_36df328680cb805f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do (CNTHCTL_read ()) ) : SailM (BitVec 32) )
              (R_set t (__get_CNTHCTL w__2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__3 ← (( do (CNTHCTL_read ()) ) : SailM (BitVec 32) )
                      (R_set t (__get_CNTHCTL w__3))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHP_CTL_SysRegRead32_5ea09b260a579171 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
              (R_set t (__get_CNTHP_CTL w__2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__3 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
                      (R_set t (__get_CNTHP_CTL w__3))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHP_TVAL_SysRegRead32_ea212b21a99af571 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
  let __CNTHP_CTL_ENABLE : (BitVec 1) := (_get_CNTHP_CTL_Type_ENABLE w__1)
  let w__2 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__CNTHP_CTL_ENABLE == 0#1) : Bool)
              then
                (do
                  let w__3 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                  (R_set t w__3))
              else
                (do
                  let w__4 ← (( do (CNTHP_CVAL_read ()) ) : SailM (BitVec 64) )
                  let w__5 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  (R_set t (Sail.BitVec.extractLsb (w__4 - w__5) 31 0))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__CNTHP_CTL_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__6 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
                          (R_set t w__6))
                      else
                        (do
                          let w__7 ← (( do (CNTHP_CVAL_read ()) ) : SailM (BitVec 64) )
                          let w__8 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (R_set t (Sail.BitVec.extractLsb (w__7 - w__8) 31 0)))))
              else (pure (())))))


end ArmFull.Functions
