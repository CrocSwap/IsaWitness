import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0044
import ArmFull.Fn.M0051
import ArmFull.Fn.M0058
import ArmFull.Fn.M0087
import ArmFull.Fn.M0121
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0189
import ArmFull.Fn.M0212
import ArmFull.Fn.M0248

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

def AArch64_AdvSIMDFPAccessTrap (target_el : (BitVec 2)) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let except ← (( do (undefined_ExceptionRecord (← occLabel 1709) ()) ) : SailM ExceptionRecord
    )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let route_to_el2 ← (( do
    if ((← do
         if (((target_el == EL1) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__2) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (route_to_el2 : Bool)
  then
    (do
      let except ← (( do (ExceptionSyndrome Exception_Uncategorized) ) : SailM ExceptionRecord )
      (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
  else
    (do
      let w__3 ← (( do (ExceptionSyndrome Exception_AdvSIMDFPAccessTrap) ) : SailM ExceptionRecord
        )
      let except : ExceptionRecord := (w__3 : ExceptionRecord)
      let w__4 ← (( do (ConditionSyndrome ()) ) : SailM (BitVec 5) )
      let except :=
        ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 24 20 w__4) } : ExceptionRecord)
      (AArch64_TakeException target_el except preferred_exception_return vect_offset))


def SVEAccessTrap (target_el : (BitVec 2)) : SailM Unit := do
  let w__2 ← (( do
    (pure ((← do
          (pure ((← do
                let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure ((((BitVec.toNat target_el) ≥b (BitVec.toNat w__0.EL)) : Bool)))) && ((target_el != EL0) : Bool)))) && ((HaveEL
          target_el) : Bool))) ) : SailM Bool )
  ArmFull.assert w__2 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:29235.86-29235.87"
  let route_to_el2 ← (( do
    if ((← do
         if (((target_el == EL1) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__5) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let except ← (( do (ExceptionSyndrome Exception_SVEAccessTrap) ) : SailM ExceptionRecord )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  if (route_to_el2 : Bool)
  then
    (do
      (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
  else
    (do
      (AArch64_TakeException target_el except preferred_exception_return vect_offset))


def SMEAccessTrap (etype : SMEExceptionType) (target_el_in : (BitVec 2)) : SailM Unit := do
  let target_el : (BitVec 2) := target_el_in
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  ArmFull.assert ((BitVec.toNat target_el) ≥b (BitVec.toNat w__0.EL)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:29351.45-29351.46"
  let target_el : (BitVec 2) :=
    if ((target_el == EL0) : Bool)
    then EL1
    else target_el
  let route_to_el2 ← (( do
    if ((← do
         if ((← do
              (pure ((← do
                    let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__1.EL == EL0) : Bool)))) && ((target_el == EL1) : Bool)))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__5) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let except ← (( do (ExceptionSyndrome Exception_SMEAccessTrap) ) : SailM ExceptionRecord )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except : ExceptionRecord :=
    match etype with
    | .SMEExceptionType_AccessTrap =>
      { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 2 0 0b000#3) }
    | .SMEExceptionType_Streaming =>
      { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 2 0 0b001#3) }
    | .SMEExceptionType_NotStreaming =>
      { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 2 0 0b010#3) }
    | .SMEExceptionType_InactiveZA =>
      { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 2 0 0b011#3) }
    | .SMEExceptionType_InaccessibleZT0 =>
      { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 2 0 0b100#3) }
  if (route_to_el2 : Bool)
  then
    (do
      (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
  else
    (do
      (AArch64_TakeException target_el except preferred_exception_return vect_offset))


def GCSDataCheckException (gcsinst_type : GCSInstruction) : SailM Unit := do
  let target_el ← (( do (undefined_bitvector_at (← occLabel 1760) 2) ) : SailM (BitVec 2) )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let rn_unknown : Bool := false
  let is_ret : Bool := false
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let target_el ← (( do
    if ((w__0.EL == EL0) : Bool)
    then
      (do
        let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__2 : (BitVec 2) :=
          if (((_get_HCR_EL2_Type_TGE w__1) == 0#1) : Bool)
          then EL1
          else EL2
        (pure ((w__2 : (BitVec 2)))))
    else
      (do
        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
        let target_el := (w__3.EL : (BitVec 2))
        (pure (target_el))) ) : SailM (BitVec 2) )
  let except ← (( do (ExceptionSyndrome Exception_GCSFail) ) : SailM ExceptionRecord )
  let (except, is_ret, rn_unknown) : (ExceptionRecord × Bool × Bool) :=
    match gcsinst_type with
    | .GCSInstType_PRET =>
      (let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 0b00000#5) }
      let is_ret : Bool := true
      (except, is_ret, rn_unknown))
    | .GCSInstType_POPM =>
      (let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 0b00001#5) }
      (except, is_ret, rn_unknown))
    | .GCSInstType_PRETAA =>
      (let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 0b00010#5) }
      let is_ret : Bool := true
      (except, is_ret, rn_unknown))
    | .GCSInstType_PRETAB =>
      (let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 0b00011#5) }
      let is_ret : Bool := true
      (except, is_ret, rn_unknown))
    | .GCSInstType_SS1 =>
      (let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 0b00100#5) }
      (except, is_ret, rn_unknown))
    | .GCSInstType_SS2 =>
      (let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 0b00101#5) }
      let rn_unknown : Bool := true
      (except, is_ret, rn_unknown))
    | .GCSInstType_POPCX =>
      (let rn_unknown : Bool := true
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 0b01000#5) }
      (except, is_ret, rn_unknown))
    | .GCSInstType_POPX =>
      (let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 0b01001#5) }
      (except, is_ret, rn_unknown))
  let except ← (( do
    if ((rn_unknown == true) : Bool)
    then
      (do
        let w__4 ← (( do (__UNKNOWN_bits 5) ) : SailM (BitVec 5) )
        let except :=
          ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5 w__4) } : ExceptionRecord)
        (pure (except)))
    else
      (do
        if ((is_ret == true) : Bool)
        then
          (do
            let w__5 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
            let except :=
              ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5
                  (Sail.BitVec.extractLsb w__5 9 5)) } : ExceptionRecord)
            (pure (except)))
        else
          (do
            let w__6 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
            let except :=
              ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5
                  (Sail.BitVec.extractLsb w__6 4 0)) } : ExceptionRecord)
            (pure (except)))) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 24 10 (Zeros (n := 15))) }
  let w__7 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let except := ({ except with vaddress := w__7 } : ExceptionRecord)
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


def EXLOCKException (_ : Unit) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_GCSFail) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 24 (Bit (Zeros (n := 1)))) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 23 20 0b0001#4) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 0 (Zeros (n := 20))) }
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (AArch64_TakeException w__0.EL except preferred_exception_return vect_offset)


def GCSSTRTrapException (target_el : (BitVec 2)) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_GCSFail) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 24 (Bit (Zeros (n := 1)))) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 23 20 0b0010#4) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 15 (Zeros (n := 5))) }
  let w__0 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
  let except :=
    ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 14 10
        (Sail.BitVec.extractLsb w__0 9 5)) } : ExceptionRecord)
  let w__1 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
  let except :=
    ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5
        (Sail.BitVec.extractLsb w__1 4 0)) } : ExceptionRecord)
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 (Zeros (n := 5))) }
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


/-- Type quantifiers: destreg : Int, k_from_epilogue : Bool, k_option_a_name : Bool, sizereg : Int, srcreg
  : Int, k_wrong_option : Bool -/
def MismatchedMemCpyException (option_a_name : Bool) (destreg : Int) (srcreg : Int) (sizereg : Int) (wrong_option : Bool) (from_epilogue : Bool) (options_name : (BitVec 4)) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let target_el ← (( do (MismatchedCpySetTargetEL ()) ) : SailM (BitVec 2) )
  let except ← (( do (ExceptionSyndrome Exception_MemCpyMemSet) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 24 (Bit 0#1)) }
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 23 (Bit 0#1)) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 22 19 options_name) }
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 18
        (Bit
          (if (from_epilogue : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 17
        (Bit
          (if (wrong_option : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 16
        (Bit
          (if (option_a_name : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 14 10
        (integer_subrange destreg 4 0)) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5
        (integer_subrange srcreg 4 0)) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0
        (integer_subrange sizereg 4 0)) }
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


/-- Type quantifiers: datareg : Int, destreg : Int, k_from_epilogue : Bool, k_is_SETG : Bool, k_option_a_name
  : Bool, sizereg : Int, k_wrong_option : Bool -/
def MismatchedMemSetException (option_a_name : Bool) (destreg : Int) (datareg : Int) (sizereg : Int) (wrong_option : Bool) (from_epilogue : Bool) (options_name : (BitVec 2)) (is_SETG : Bool) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let target_el ← (( do (MismatchedCpySetTargetEL ()) ) : SailM (BitVec 2) )
  let except ← (( do (ExceptionSyndrome Exception_MemCpyMemSet) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 24 (Bit 1#1)) }
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 23
        (Bit
          (if (is_SETG : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 20 19 options_name) }
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 18
        (Bit
          (if (from_epilogue : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 17
        (Bit
          (if (wrong_option : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 16
        (Bit
          (if (option_a_name : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 14 10
        (integer_subrange destreg 4 0)) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5
        (integer_subrange datareg 4 0)) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0
        (integer_subrange sizereg 4 0)) }
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


/-- Type quantifiers: dreg : Int -/
def TransactionStartTrap (dreg : Int) : SailM Unit := do
  let targetEL ← (( do (undefined_bitvector_at (← occLabel 1937) 2) ) : SailM (BitVec 2) )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_TSTARTAccessTrap) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5
        (integer_subrange dreg 4 0)) }
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let targetEL ← (( do
    if (((BitVec.toNat w__0.EL) >b (BitVec.toNat EL1)) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        let targetEL := (w__1.EL : (BitVec 2))
        (pure (targetEL)))
    else
      (do
        let w__4 ← (( do
          if ((← do
               (EL2Enabled ())) : Bool)
          then
            (do
              let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_HCR_EL2_Type_TGE w__3) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let targetEL : (BitVec 2) :=
          if (w__4 : Bool)
          then EL2
          else EL1
        (pure (targetEL))) ) : SailM (BitVec 2) )
  (AArch64_TakeException targetEL except preferred_exception_return vect_offset)


def AArch64_CallSecureMonitor (immediate : (BitVec 16)) : SailM Unit := do
  let w__1 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        (pure (((! w__0) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__1 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:33567.54-33567.55"
  let w__2 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (AArch32_ITAdvance ()))
  else (pure (()))
  (SSAdvance ())
  let preferred_exception_return ← (( do (NextInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_MonitorCall) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
  (AArch64_TakeException EL3 except preferred_exception_return vect_offset)


def AArch64_CallHypervisor (immediate : (BitVec 16)) : SailM Unit := do
  ArmFull.assert (HaveEL EL2) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:33582.22-33582.23"
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (AArch32_ITAdvance ()))
  else (pure (()))
  (SSAdvance ())
  let preferred_exception_return ← (( do (NextInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_HypervisorCall) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__1.EL == EL3) : Bool)
  then
    (do
      (AArch64_TakeException EL3 except preferred_exception_return vect_offset))
  else
    (do
      (AArch64_TakeException EL2 except preferred_exception_return vect_offset))


def AArch64_CallSupervisor (immediate_in : (BitVec 16)) : SailM Unit := do
  let immediate : (BitVec 16) := immediate_in
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (AArch32_ITAdvance ()))
  else (pure (()))
  (SSAdvance ())
  let route_to_el2 ← (( do
    if ((← do
         if ((← do
              let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__1.EL == EL0) : Bool)))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__4) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (NextInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_SupervisorCall) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  if (((BitVec.toNat w__5.EL) >b (BitVec.toNat EL1)) : Bool)
  then
    (do
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      (AArch64_TakeException w__6.EL except preferred_exception_return vect_offset))
  else
    (do
      if (route_to_el2 : Bool)
      then
        (do
          (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
      else
        (do
          (AArch64_TakeException EL1 except preferred_exception_return vect_offset)))


def AArch64_UndefinedFault (_ : Unit) : SailM Unit := do
  let route_to_el2 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__3) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_Uncategorized) ) : SailM ExceptionRecord )
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  if (((BitVec.toNat w__4.EL) >b (BitVec.toNat EL1)) : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      (AArch64_TakeException w__5.EL except preferred_exception_return vect_offset))
  else
    (do
      if (route_to_el2 : Bool)
      then
        (do
          (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
      else
        (do
          (AArch64_TakeException EL1 except preferred_exception_return vect_offset)))


def AArch64_CheckIllegalState (_ : Unit) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (.site 2402) ()) ) : SailM ExceptionRecord )
  let route_to_el2 ← (( do (undefined_bool_at (.site 2403) ()) ) : SailM Bool )
  let vect_offset ← (( do (undefined_int_at (.site 2404) ()) ) : SailM Int )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.IL == 1#1) : Bool)
  then
    (do
      let route_to_el2 ← (( do
        if ((← do
             if ((← do
                  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__1.EL == EL0) : Bool)))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_TGE w__4) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
      let vect_offset : Int := (BitVec.toNat 0x0#4)
      let except ← (( do (ExceptionSyndrome Exception_IllegalState) ) : SailM ExceptionRecord )
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      if (((BitVec.toNat w__5.EL) >b (BitVec.toNat EL1)) : Bool)
      then
        (do
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          (AArch64_TakeException w__6.EL except preferred_exception_return vect_offset))
      else
        (do
          if (route_to_el2 : Bool)
          then
            (do
              (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
          else
            (do
              (AArch64_TakeException EL1 except preferred_exception_return vect_offset))))
  else (pure (()))


def LDST64BTrap (target_el : (BitVec 2)) (iss : (BitVec 25)) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_LDST64BTrap) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with syndrome := iss }
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


/-- Type quantifiers: k_eret_with_pac : Bool, k_pac_uses_key_a : Bool -/
def AArch64_CheckForERetTrap (eret_with_pac : Bool) (pac_uses_key_a : Bool) : SailM Unit := do
  let vect_offset ← (( do (undefined_int_at (← occLabel 2408) ()) ) : SailM Int )
  let route_to_el2 : Bool := false
  let route_to_el2 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL1) : Bool)))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  (HaveNVExt ())) : Bool)
             then
               (do
                 let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_NV w__4) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      (HaveFGTExt ())) : Bool)
                 then
                   (do
                     if (((! (HaveEL EL3)) : Bool) : Bool)
                     then (pure true)
                     else
                       (do
                         let w__7 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_SCR_EL3_Type_FGTEn w__7) == 1#1) : Bool)))))
                 else (pure false)) : Bool)
            then
              (do
                let w__10 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HFGITR_EL2_Type_ERET w__10) == 1#1) : Bool))))
            else (pure false)))
    else (pure false) ) : SailM Bool )
  if (route_to_el2 : Bool)
  then
    (do
      let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
      let vect_offset : Int := (BitVec.toNat 0x0#4)
      let except ← (( do (ExceptionSyndrome Exception_ERetTrap) ) : SailM ExceptionRecord )
      let except : ExceptionRecord :=
        if ((! eret_with_pac) : Bool)
        then
          (let except : ExceptionRecord :=
            { except with syndrome := (BitVec.update except.syndrome 1 (Bit 0#1)) }
          { except with syndrome := (BitVec.update except.syndrome 0 (Bit 0#1)) })
        else
          (let except : ExceptionRecord :=
            { except with syndrome := (BitVec.update except.syndrome 1 (Bit 1#1)) }
          if (pac_uses_key_a : Bool)
          then { except with syndrome := (BitVec.update except.syndrome 0 (Bit 0#1)) }
          else { except with syndrome := (BitVec.update except.syndrome 0 (Bit 1#1)) })
      (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
  else (pure (()))


def AArch64_CheckForSVCTrap (immediate : (BitVec 16)) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2409) ()) ) : SailM ExceptionRecord
    )
  let route_to_el2 ← (( do (undefined_bool_at (← occLabel 2410) ()) ) : SailM Bool )
  let vect_offset ← (( do (undefined_int_at (← occLabel 2411) ()) ) : SailM Int )
  let w__0 ← (( do (HaveFGTExt ()) ) : SailM Bool )
  let route_to_el2 ← (( do
    if (w__0 : Bool)
    then
      (do
        let route_to_el2 : Bool := false
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        let route_to_el2 ← (( do
          if ((w__1.EL == EL0) : Bool)
          then
            (do
              if ((← do
                   if ((← do
                        if ((← do
                             if ((← do
                                  let w__2 ← (( do (UsingAArch32 ()) ) : SailM Bool )
                                  (pure (((! w__2) : Bool)))) : Bool)
                             then
                               (do
                                 let w__3 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                                 (pure (((! w__3) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            (EL2Enabled ()))
                        else (pure false)) : Bool)
                   then
                     (do
                       let w__7 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
                       (pure ((((_get_HFGITR_EL2_Type_SVC_EL0 w__7) == 1#1) : Bool))))
                   else (pure false)) : Bool)
              then
                (do
                  if ((← do
                       let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       (pure (((((_get_HCR_EL2_Type_E2H w__9) +++ (_get_HCR_EL2_Type_TGE w__10)) != 0b11#2) : Bool)))) : Bool)
                  then
                    (do
                      if (((! (HaveEL EL3)) : Bool) : Bool)
                      then (pure true)
                      else
                        (do
                          let w__11 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                          (pure ((((_get_SCR_EL3_Type_FGTEn w__11) == 1#1) : Bool)))))
                  else (pure false))
              else (pure false))
          else
            (do
              let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__15.EL == EL1) : Bool)
              then
                (do
                  if ((← do
                       if ((← do
                            (EL2Enabled ())) : Bool)
                       then
                         (do
                           let w__17 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
                           (pure ((((_get_HFGITR_EL2_Type_SVC_EL1 w__17) == 1#1) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      if (((! (HaveEL EL3)) : Bool) : Bool)
                      then (pure true)
                      else
                        (do
                          let w__19 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                          (pure ((((_get_SCR_EL3_Type_FGTEn w__19) == 1#1) : Bool)))))
                  else (pure false))
              else (pure (route_to_el2))) ) : SailM Bool )
        if (route_to_el2 : Bool)
        then
          (do
            let w__22 ← (( do (ExceptionSyndrome Exception_SupervisorCall) ) : SailM
              ExceptionRecord )
            let except : ExceptionRecord := (w__22 : ExceptionRecord)
            let except : ExceptionRecord :=
              { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
            let except : ExceptionRecord := { except with trappedsyscallinst := true }
            let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
            let vect_offset : Int := (BitVec.toNat 0x0#4)
            (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
        else (pure (()))
        (pure (route_to_el2)))
    else (pure (route_to_el2)) ) : SailM Bool )
  let route_to_el2 := route_to_el2
  (pure (()))


end ArmFull.Functions
