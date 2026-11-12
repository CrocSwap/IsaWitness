import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0034
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0041
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0046
import ArmFull.Fn.M0056
import ArmFull.Fn.M0061
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0098
import ArmFull.Fn.M0099
import ArmFull.Fn.M0113
import ArmFull.Fn.M0115
import ArmFull.Fn.M0121
import ArmFull.Fn.M0123
import ArmFull.Fn.M0124

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

def AArch32_ReportedInnerAttrs (attrs : (BitVec 3)) : SailM (BitVec 3) := do
  (__UNKNOWN_bits 3)


def AArch32_ReportedOuterAttrs (attrs : (BitVec 2)) : SailM (BitVec 2) := do
  (__UNKNOWN_bits 2)


/-- Type quantifiers: k_N : Nat, amount : Int, k_N ≥ 0 -/
def Shift_C (value_name : (BitVec k_N)) (srtype : SRType) (amount : Int) (carry_in : (BitVec 1)) : SailM ((BitVec k_N) × (BitVec 1)) := do
  ArmFull.assert (! ((BEq.beq srtype SRType_RRX) && (amount != 1))) "sail-arm/v8_base.sail:41274.55-41274.56"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2695)
      (Sail.BitVec.length value_name))) ) : SailM (BitVec k_N) )
  let carry_out ← (( do (undefined_bitvector_at (← occLabel 2696) 1) ) : SailM (BitVec 1) )
  let (carry_out, result) ← (( do
    if ((amount == 0) : Bool)
    then
      (let (tup__0, tup__1) := ((value_name, carry_in) : ((BitVec k_N) × (BitVec 1)))
      let result : (BitVec k_N) := tup__0
      let carry_out : (BitVec 1) := tup__1
      (pure ((carry_out, result))))
    else
      (do
        match srtype with
        | .SRType_LSL =>
          (let (tup__0, tup__1) := ((LSL_C value_name amount) : ((BitVec k_N) × (BitVec 1)))
          let result : (BitVec k_N) := tup__0
          let carry_out : (BitVec 1) := tup__1
          (pure ((carry_out, result))))
        | .SRType_LSR =>
          (let (tup__0, tup__1) := ((LSR_C value_name amount) : ((BitVec k_N) × (BitVec 1)))
          let result : (BitVec k_N) := tup__0
          let carry_out : (BitVec 1) := tup__1
          (pure ((carry_out, result))))
        | .SRType_ASR =>
          (do
            ArmFull.assert (((Sail.BitVec.length value_name) ≥b 0) && (amount ≥b 0)) "sail-arm/v8_base.sail:41288.57-41288.58"
            let (tup__0, tup__1) :=
              ((ASR_C value_name (Sail.Int.toNatChecked (amount))) : ((BitVec k_N) × (BitVec 1)))
            let result : (BitVec k_N) := tup__0
            let carry_out : (BitVec 1) := tup__1
            (pure ((carry_out, result))))
        | .SRType_ROR =>
          (do
            ArmFull.assert ((Sail.BitVec.length value_name) >b 0) "sail-arm/v8_base.sail:41292.39-41292.40"
            let w__0 ← (( do (ROR_C value_name amount) ) : SailM ((BitVec k_N) × (BitVec 1)) )
            let (tup__0, tup__1) := (w__0 : ((BitVec k_N) × (BitVec 1)))
            let result : (BitVec k_N) := tup__0
            let carry_out : (BitVec 1) := tup__1
            (pure ((carry_out, result))))
        | .SRType_RRX =>
          (do
            ArmFull.assert ((Sail.BitVec.length value_name) >b 1) "sail-arm/v8_base.sail:41296.39-41296.40"
            let (tup__0, tup__1) := ((RRX_C value_name carry_in) : ((BitVec k_N) × (BitVec 1)))
            let result : (BitVec k_N) := tup__0
            let carry_out : (BitVec 1) := tup__1
            (pure ((carry_out, result))))) ) : SailM ((BitVec 1) × (BitVec k_N)) )
  (pure ((result, carry_out)))


def T32ExpandImm (imm12 : (BitVec 12)) : SailM (BitVec 32) := do
  let imm32 ← (( do (undefined_bitvector_at (← occLabel 2707) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let (__tup_0, _) ← (( do (T32ExpandImm_C imm12 w__0.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  (pure (__tup_0))


def StandardFPSCRValue (_ : Unit) : SailM (BitVec 64) := do
  let w__0 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
  let w__1 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
  let value_name : (BitVec 32) :=
    ((((0b00000#5 +++ (_get_FPSCR_Type_AHP w__0)) +++ 0b110000#6) +++ (_get_FPSCR_Type_FZ16 w__1)) +++ 0b0000000000000000000#19)
  (pure ((Mk_FPCRType (Sail.BitVec.zeroExtend value_name 64))))


def AArch32_ResetSpecialRegisters (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg SPSR_fiq ) : SailM (BitVec 64) )
  let w__1 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  writeReg SPSR_fiq (Sail.BitVec.updateSubrange w__0 31 0 w__1)
  let w__2 ← (( do readReg SPSR_irq ) : SailM (BitVec 64) )
  let w__3 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  writeReg SPSR_irq (Sail.BitVec.updateSubrange w__2 31 0 w__3)
  let w__4 ← (( do (SPSR_svc_read ()) ) : SailM (BitVec 32) )
  let w__5 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (SPSR_svc_write (Mk_SPSR_svc_Type (Sail.BitVec.updateSubrange w__4 31 0 w__5)))
  let w__6 ← (( do readReg SPSR_abt ) : SailM (BitVec 64) )
  let w__7 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  writeReg SPSR_abt (Sail.BitVec.updateSubrange w__6 31 0 w__7)
  let w__8 ← (( do readReg SPSR_und ) : SailM (BitVec 64) )
  let w__9 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  writeReg SPSR_und (Sail.BitVec.updateSubrange w__8 31 0 w__9)
  if ((HaveEL EL2) : Bool)
  then
    (do
      let w__10 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (SPSR_hyp_write (Mk_SPSR_hyp_Type w__10))
      let w__11 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (ELR_hyp_write w__11))
  else (pure (()))
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__12 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      writeReg SPSR_mon (Mk_SPSR_mon_Type w__12))
  else (pure (()))
  let w__13 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (DLR_write w__13)
  let w__14 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (DSPSR_write (Mk_DSPSR_Type w__14))


/-- Type quantifiers: N : Nat, i : Int, 0 ≤ (N - 1) -/
def UnsignedSat (i : Int) (N : Nat) : SailM (BitVec N) := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2768)
      (Sail.Int.toNatChecked (N)))) ) : SailM (BitVec N) )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (UnsignedSatQ i N)) ) : SailM
    ((BitVec N) × Bool) )
  (pure ((Sail.BitVec.castWidth __tup_0)))


/-- Type quantifiers: N : Nat, i : Int, 0 ≤ (N - 1) -/
def SignedSat (i : Int) (N : Nat) : SailM (BitVec N) := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2769)
      (Sail.Int.toNatChecked (N)))) ) : SailM (BitVec N) )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ i N)) ) : SailM
    ((BitVec N) × Bool) )
  (pure ((Sail.BitVec.castWidth __tup_0)))


def AArch32_DTLBI_ALL (security : SecurityState) (regime : Regime) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:43614.65-43614.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2797) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_DALL }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_DTLBI_ASID (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:43632.65-43632.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2798) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_DASID }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_DTLBI_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:43652.65-43652.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2799) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_DVA }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  let r : TLBIRecord :=
    { r with address := (((Zeros (n := 32)) +++ (Sail.BitVec.extractLsb Rt 31 12)) +++ (Zeros
          (n := 12))) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_ITLBI_ALL (security : SecurityState) (regime : Regime) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:43673.65-43673.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2800) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IALL }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_ITLBI_ASID (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:43691.65-43691.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2801) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IASID }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_ITLBI_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:43711.65-43711.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2802) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IVA }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  let r : TLBIRecord :=
    { r with address := (((Zeros (n := 32)) +++ (Sail.BitVec.extractLsb Rt 31 12)) +++ (Zeros
          (n := 12))) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_TLBI_ALL (security : SecurityState) (regime : Regime) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL2) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "sail-arm/v8_base.sail:43732.46-43732.47"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2803) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_ALL }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_TLBI_VMALL (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:43750.65-43750.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2804) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VMALL }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_TLBI_ASID (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:43769.65-43769.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2805) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_ASID }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_TLBI_VA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:43789.65-43789.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2806) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VA }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := ((Zeros (n := 8)) +++ (Sail.BitVec.extractLsb Rt 7 0)) }
  let r : TLBIRecord :=
    { r with address := (((Zeros (n := 32)) +++ (Sail.BitVec.extractLsb Rt 31 12)) +++ (Zeros
          (n := 12))) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_TLBI_VAA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:43810.65-43810.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2807) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VAA }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord :=
    { r with address := (((Zeros (n := 32)) +++ (Sail.BitVec.extractLsb Rt 31 12)) +++ (Zeros
          (n := 12))) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_TLBI_IPAS2 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Rt : (BitVec 32)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL2) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "sail-arm/v8_base.sail:43830.46-43830.47"
  ArmFull.assert (BEq.beq security SS_NonSecure) "sail-arm/v8_base.sail:43831.35-43831.36"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2808) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_IPAS2 }
  let r : TLBIRecord := { r with from_aarch64 := false }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord :=
    { r with address := (((Zeros (n := 24)) +++ (Sail.BitVec.extractLsb Rt 27 0)) +++ (Zeros
          (n := 12))) }
  let r : TLBIRecord := { r with ipaspace := PAS_NonSecure }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def __set_PMCR_EL0 (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMCR_EL0_Type := value_name
  let w__0 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (BitVec.update w__0 0 (Bit (BitVec.slice r 0 1)))
  let w__1 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__1 15 3 (BitVec.slice r 3 13))
  let w__2 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__2 63 32 (BitVec.slice r 32 32))
  let w__3 ← (( do (IsFeatureImplemented FEAT_PMUv3p7) ) : SailM Bool )
  if ((! (! w__3)) : Bool)
  then
    (do
      let w__4 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
      writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__4 31 24 (_get_PMCR_EL0_Type_IMP r)))
  else (pure (()))
  let w__5 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  if ((! ((_get_PMCR_EL0_Type_IMP w__5) != 0b00000000#8)) : Bool)
  then
    (do
      let w__6 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
      writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__6 23 16 (_get_PMCR_EL0_Type_IDCODE r)))
  else (pure (()))
  let w__7 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__7 2 2 (_get_PMCR_EL0_Type_C r))
  let w__8 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__8 1 1 (_get_PMCR_EL0_Type_P r))


def __set_MPAM3_EL3 (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM3_EL3_Type := value_name
  let w__0 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (Mk_MPAM3_EL3_Type (set_slice 63 w__0 0 (BitVec.slice r 0 63))))
  let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (_update_MPAM3_EL3_Type_MPAMEN w__1 (_get_MPAM3_EL3_Type_MPAMEN r)))


def __set_PMCR (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCR_Type := value_name
  let w__0 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (Mk_PMCR_Type (set_slice 1 w__0 0 (BitVec.slice r 0 1))))
  let w__1 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (Mk_PMCR_Type (set_slice 13 w__1 3 (BitVec.slice r 3 13))))
  let w__2 ← (( do (IsFeatureImplemented FEAT_PMUv3p7) ) : SailM Bool )
  if ((! (! w__2)) : Bool)
  then
    (do
      let w__3 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
      (PMCR_write (_update_PMCR_Type_IMP w__3 (_get_PMCR_Type_IMP r))))
  else (pure (()))
  let w__4 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  if ((! ((_get_PMCR_Type_IMP w__4) != 0b00000000#8)) : Bool)
  then
    (do
      let w__5 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
      (PMCR_write (_update_PMCR_Type_IDCODE w__5 (_get_PMCR_Type_IDCODE r))))
  else (pure (()))
  let w__6 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (_update_PMCR_Type_C w__6 (_get_PMCR_Type_C r)))
  let w__7 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (_update_PMCR_Type_P w__7 (_get_PMCR_Type_P r)))


def __get_OSDLR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : OSDLR_EL1_Type := value_name
  let w__0 ← (( do (IsFeatureImplemented FEAT_DoubleLock) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__0) : Bool)
    then
      (Mk_OSDLR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x1#4 64)))))
    else tmp
  let tmp : OSDLR_EL1_Type :=
    (Mk_OSDLR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFE#64)))
  (pure (tmp))


def __get_SCR_EL3 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : SCR_EL3_Type := value_name
  let tmp : SCR_EL3_Type :=
    (Mk_SCR_EL3_Type
      ((tmp &&& (Complement.complement 0xB744000001C00040#64)) ||| (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend
          0x30#8 64))))
  if ((! ((HaveAArch32EL EL1) || (HaveAArch32EL EL2))) : Bool)
  then
    (Mk_SCR_EL3_Type
      ((Sail.BitVec.castWidth (m := 64) (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x0#4 64))))) ||| (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend
          0x400#12 64))))
  else tmp


end ArmFull.Functions
