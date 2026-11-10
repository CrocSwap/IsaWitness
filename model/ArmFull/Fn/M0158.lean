import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0020
import ArmFull.Fn.M0024
import ArmFull.Fn.M0039
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0049
import ArmFull.Fn.M0054
import ArmFull.Fn.M0061
import ArmFull.Fn.M0062
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0117
import ArmFull.Fn.M0123
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0149

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

def EncodePARange (_ : Unit) : SailM (BitVec 4) := do
  let w__0 ← (( do readReg __supported_pa_size ) : SailM Int )
  match w__0 with
  | 32 => (pure (0b0000#4))
  | 36 => (pure (0b0001#4))
  | 40 => (pure (0b0010#4))
  | 42 => (pure (0b0011#4))
  | 44 => (pure (0b0100#4))
  | 48 => (pure (0b0101#4))
  | 52 =>
    (do
      let w__1 ← (( do (Have52BitPAExt ()) ) : SailM Bool )
      ArmFull.assert w__1 "/home/doug/boss-scratch/sail-lean-fork/integ/model/reset.sail:79.33-79.34"
      (pure (0b0110#4)))
  | 56 =>
    (do
      let w__2 ← (( do (Have56BitPAExt ()) ) : SailM Bool )
      ArmFull.assert w__2 "/home/doug/boss-scratch/sail-lean-fork/integ/model/reset.sail:83.33-83.34"
      (pure (0b0111#4)))
  | _ => (pure (0b0110#4))


def EncodeVARange (_ : Unit) : SailM (BitVec 4) := do
  let w__0 ← (( do readReg __supported_va_size ) : SailM Int )
  match w__0 with
  | 48 => (pure (0b0000#4))
  | 52 =>
    (do
      let w__1 ← (( do (Have52BitVAExt ()) ) : SailM Bool )
      ArmFull.assert w__1 "/home/doug/boss-scratch/sail-lean-fork/integ/model/reset.sail:98.33-98.34"
      (pure (0b0001#4)))
  | 56 =>
    (do
      let w__2 ← (( do (Have56BitVAExt ()) ) : SailM Bool )
      ArmFull.assert w__2 "/home/doug/boss-scratch/sail-lean-fork/integ/model/reset.sail:102.33-102.34"
      (pure (0b0001#4)))
  | _ =>
    (do
      (undefined_bitvector_at (← occLabel 2400) 4))


def SPEResetSampleStorage (_ : Unit) : SailM Unit := do
  writeReg SPESampleContextEL1 (Zeros (n := 32))
  writeReg SPESampleContextEL1Valid false
  writeReg SPESampleContextEL2 (Zeros (n := 32))
  writeReg SPESampleContextEL2Valid false
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := (Sail.Int.toNatChecked ((SPEMaxCounters -i 1)))
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do readReg SPESampleCounter ) : SailM (Vector Int 32) )
        writeReg SPESampleCounter (vectorUpdate w__0 (Sail.Int.toNatChecked (i)) 0)
        let w__1 ← (( do readReg SPESampleCounterValid ) : SailM (Vector Bool 32) )
        writeReg SPESampleCounterValid (vectorUpdate w__1 (Sail.Int.toNatChecked (i)) false)
        let w__2 ← (( do readReg SPESampleCounterPending ) : SailM (Vector Bool 32) )
        writeReg SPESampleCounterPending (vectorUpdate w__2 (Sail.Int.toNatChecked (i)) false)
    (pure loop_vars))
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := (Sail.Int.toNatChecked ((SPEMaxAddrs -i 1)))
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__3 ← (( do readReg SPESampleAddressValid ) : SailM (Vector Bool 32) )
        writeReg SPESampleAddressValid (vectorUpdate w__3 (Sail.Int.toNatChecked (i)) false)
        let w__4 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
        writeReg SPESampleAddress (vectorUpdate w__4 (Sail.Int.toNatChecked (i)) (Zeros (n := 64)))
    (pure loop_vars))
  writeReg SPESampleDataSource (Zeros (n := 16))
  writeReg SPESampleDataSourceValid false
  writeReg SPESampleClass (Zeros (n := 2))
  writeReg SPESampleSubclass (Zeros (n := 8))
  writeReg SPESampleSubclassValid false
  writeReg SPESampleTimestamp (Zeros (n := 64))
  writeReg SPESampleTimestampValid false
  let w__5 ← (( do readReg SPESampleEvents ) : SailM (BitVec 64) )
  let w__6 ← (( do (__IMPDEF_bits 16 "SPE EVENTS 63_48") ) : SailM (BitVec 16) )
  writeReg SPESampleEvents (Sail.BitVec.updateSubrange w__5 63 48 w__6)
  let w__7 ← (( do readReg SPESampleEvents ) : SailM (BitVec 64) )
  writeReg SPESampleEvents (Sail.BitVec.updateSubrange w__7 47 32 (Zeros (n := 16)))
  let w__8 ← (( do readReg SPESampleEvents ) : SailM (BitVec 64) )
  let w__9 ← (( do (__IMPDEF_bits 8 "SPE EVENTS 31_24") ) : SailM (BitVec 8) )
  writeReg SPESampleEvents (Sail.BitVec.updateSubrange w__8 31 24 w__9)
  let w__10 ← (( do readReg SPESampleEvents ) : SailM (BitVec 64) )
  writeReg SPESampleEvents (Sail.BitVec.updateSubrange w__10 23 16 (Zeros (n := 8)))
  let w__11 ← (( do readReg SPESampleEvents ) : SailM (BitVec 64) )
  let w__12 ← (( do (__IMPDEF_bits 4 "SPE EVENTS 15_12") ) : SailM (BitVec 4) )
  writeReg SPESampleEvents (Sail.BitVec.updateSubrange w__11 15 12 w__12)
  let w__13 ← (( do readReg SPESampleEvents ) : SailM (BitVec 64) )
  writeReg SPESampleEvents (Sail.BitVec.updateSubrange w__13 11 0 (Zeros (n := 12)))
  writeReg SPESampleInstIsNV2 false


def SPECycle (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (()))
  else
    (do
      let w__1 ← (( do readReg SPESampleInFlight ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := (Sail.Int.toNatChecked ((SPEMaxCounters -i 1)))
          (do
            let mut loop_vars := ()
            for i in [loop_i_lower:loop_i_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                let w__2 ← (( do readReg SPESampleCounterPending ) : SailM (Vector Bool 32) )
                if ((GetElem?.getElem! w__2 (Sail.Int.toNatChecked (i))) : Bool)
                then
                  (do
                    let w__3 ← (( do readReg SPESampleCounter ) : SailM (Vector Int 32) )
                    let w__4 ← (( do readReg SPESampleCounter ) : SailM (Vector Int 32) )
                    writeReg SPESampleCounter (vectorUpdate w__3 (Sail.Int.toNatChecked (i))
                      ((GetElem?.getElem! w__4 (Sail.Int.toNatChecked (i))) +i 1)))
                else (pure (()))
            (pure loop_vars)))
      else (pure (()))
      let w__5 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
      let w__6 : Signal :=
        if (((_get_PMBSR_EL1_Type_S w__5) == 1#1) : Bool)
        then Signal_High
        else Signal_Low
      (SetInterruptRequestLevel InterruptID_PMBIRQ w__6))


/-- Type quantifiers: N : Nat, reg : Int, shift : Int, N ≥ 0 ∧
  N = 8 ∨
  N = 16 ∨
  N = 32 ∨
  N = 64 ∨
  (not ((Sail.Int.toNatChecked (shift : Int)) ≥ 0 ∧ (Sail.Int.toNatChecked (shift : Int)) ≤ 4)) -/
def ExtendReg (reg : Int) (exttype : ExtendType) (shift : Int) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((shift ≥b 0) && (shift ≤b 4)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:35781.34-35781.35"
  let val_name ← (( do ((Sail.BitVec.castWidth ) <$> (X_read reg N)) ) : SailM (BitVec N) )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 2457) ()) ) : SailM Bool )
  let len ← (( do (undefined_int_at (← occLabel 2458) ()) ) : SailM Int )
  let (is_unsigned, len) : (Bool × Int) :=
    match exttype with
    | .ExtendType_SXTB =>
      (let is_unsigned : Bool := false
      let len : Int := 8
      (is_unsigned, len))
    | .ExtendType_SXTH =>
      (let is_unsigned : Bool := false
      let len : Int := 16
      (is_unsigned, len))
    | .ExtendType_SXTW =>
      (let is_unsigned : Bool := false
      let len : Int := 32
      (is_unsigned, len))
    | .ExtendType_SXTX =>
      (let is_unsigned : Bool := false
      let len : Int := 64
      (is_unsigned, len))
    | .ExtendType_UXTB =>
      (let is_unsigned : Bool := true
      let len : Int := 8
      (is_unsigned, len))
    | .ExtendType_UXTH =>
      (let is_unsigned : Bool := true
      let len : Int := 16
      (is_unsigned, len))
    | .ExtendType_UXTW =>
      (let is_unsigned : Bool := true
      let len : Int := 32
      (is_unsigned, len))
    | .ExtendType_UXTX =>
      (let is_unsigned : Bool := true
      let len : Int := 64
      (is_unsigned, len))
  let is_unsigned := is_unsigned
  let len : Int := (Min.min len (N -i shift))
  ArmFull.assert ((0 ≤b (len -i 1)) || (! ((shift ≥b 0) && (shift ≤b 4)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:35821.73-35821.74"
  ((Sail.BitVec.castWidth ) <$> (Extend
    ((Sail.BitVec.extractLsb val_name (Sail.Int.toNatChecked ((len -i 1))) 0) +++ (Zeros
        (n := (Sail.Int.toNatChecked (shift))))) N is_unsigned))


/-- Type quantifiers: N : Nat, amount : Int, reg : Int, List.elem N [8, 16, 32, 64] -/
def ShiftReg (reg : Int) (shiftype : ShiftType) (amount : Int) (N : Nat) : SailM (BitVec N) := do
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (X_read reg N)) ) : SailM (BitVec N) )
  match shiftype with
  | .ShiftType_LSL =>
    (let result : (BitVec N) := (result <<< amount)
    (pure (result)))
  | .ShiftType_LSR =>
    (let result : (BitVec N) := (result >>> amount)
    (pure (result)))
  | .ShiftType_ASR =>
    (let result : (BitVec N) := (BitVec.sshiftRight result (Sail.Int.toNatChecked (amount)))
    (pure (result)))
  | .ShiftType_ROR =>
    (do
      ArmFull.assert ((N >b 0) && (amount ≥b 0)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:35864.52-35864.53"
      let result : (BitVec N) := (ROR result (Sail.Int.toNatChecked (amount)))
      (pure (result)))


def HasLargeAddress (regime : Regime) : SailM Bool := do
  let w__0 ← (( do (Have52BitIPAAndPASpaceExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      match regime with
      | .Regime_EL3 =>
        (do
          let w__1 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
          (pure (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__1 32)])) == 1#1))))
      | .Regime_EL2 =>
        (do
          let w__2 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
          (pure (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__2 32)])) == 1#1))))
      | .Regime_EL20 =>
        (do
          let w__3 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
          (pure (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__3 59)])) == 1#1))))
      | .Regime_EL10 =>
        (do
          let w__4 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
          (pure (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__4 59)])) == 1#1))))
      | _ =>
        (do
          (Unreachable ())
          (undefined_bool_at (← occLabel 2471) ())))


def AArch64_TLBIP_RVA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 128)) : SailM Unit := do
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
  ArmFull.assert w__4 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36325.65-36325.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2474) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RVA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := (Sail.BitVec.extractLsb Xt 63 48) }
  let r : TLBIRecord :=
    { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord :=
    { r with d64 := ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb r.ttl 1 0)) == 0b00#2) }
  let r : TLBIRecord := { r with d128 := true }
  let valid_name ← (( do (undefined_bool_at (← occLabel 2475) ()) ) : SailM Bool )
  let w__5 ← (( do (TLBIPRange regime Xt) ) : SailM
    (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)) )
  let (tup__0, tup__1, tup__2, tup__3) :=
    (w__5 : (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)))
  let valid_name : Bool := tup__0
  let r : TLBIRecord := { r with tg := tup__1 }
  let r : TLBIRecord := { r with address := tup__2 }
  let r : TLBIRecord := { r with end_address_name := tup__3 }
  if ((! valid_name) : Bool)
  then (pure (()))
  else
    (do
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure (())))


def AArch64_TLBIP_RVAA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 128)) : SailM Unit := do
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
  ArmFull.assert w__4 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36384.65-36384.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2478) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RVAA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord :=
    { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord :=
    { r with d64 := ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb r.ttl 1 0)) == 0b00#2) }
  let r : TLBIRecord := { r with d128 := true }
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let baseaddr : Int := (BitVec.toInt (Sail.BitVec.extractLsb Xt 36 0))
  let valid_name ← (( do (undefined_bool_at (← occLabel 2479) ()) ) : SailM Bool )
  let w__5 ← (( do (TLBIPRange regime Xt) ) : SailM
    (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)) )
  let (tup__0, tup__1, tup__2, tup__3) :=
    (w__5 : (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)))
  let valid_name : Bool := tup__0
  let r : TLBIRecord := { r with tg := tup__1 }
  let r : TLBIRecord := { r with address := tup__2 }
  let r : TLBIRecord := { r with end_address_name := tup__3 }
  if ((! valid_name) : Bool)
  then (pure (()))
  else
    (do
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure (())))


def AArch64_TLBIP_RIPAS2 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 128)) : SailM Unit := do
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
  ArmFull.assert w__4 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36460.65-36460.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2482) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RIPAS2 }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord :=
    { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord :=
    { r with d64 := ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb r.ttl 1 0)) == 0b00#2) }
  let r : TLBIRecord := { r with d128 := true }
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let baseaddr : Int := (BitVec.toInt (Sail.BitVec.extractLsb Xt 36 0))
  let valid_name ← (( do (undefined_bool_at (← occLabel 2483) ()) ) : SailM Bool )
  let w__5 ← (( do (TLBIPRange regime Xt) ) : SailM
    (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)) )
  let (tup__0, tup__1, tup__2, tup__3) :=
    (w__5 : (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)))
  let valid_name : Bool := tup__0
  let r : TLBIRecord := { r with tg := tup__1 }
  let r : TLBIRecord := { r with address := tup__2 }
  let r : TLBIRecord := { r with end_address_name := tup__3 }
  if ((! valid_name) : Bool)
  then (pure (()))
  else
    (do
      let r ← (( do
        match security with
        | .SS_NonSecure =>
          (let r : TLBIRecord := { r with ipaspace := PAS_NonSecure }
          (pure (r)))
        | .SS_Secure =>
          (let r : TLBIRecord :=
            { r with ipaspace := if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 63)])) == 1#1) : Bool)
              then PAS_NonSecure
              else PAS_Secure }
          (pure (r)))
        | .SS_Realm =>
          (let r : TLBIRecord := { r with ipaspace := PAS_Realm }
          (pure (r)))
        | _ =>
          (do
            (Unreachable ())
            (pure (r))) ) : SailM TLBIRecord )
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure (())))


def AArch64_TLBI_RPA (level : TLBILevel) (Xt : (BitVec 64)) (shareability : Shareability) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         (HaveRME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL3) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__2 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36505.39-36505.40"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2484) ()) ) : SailM TLBIRecord )
  let range_bits ← (( do (undefined_int_at (← occLabel 2485) ()) ) : SailM Int )
  let p : Int := 12
  let r : TLBIRecord := { r with op := TLBIOp_RPA }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := TLBI_AllAttr }
  let range_bits : Int :=
    match (BitVec.setWidth 4 (Sail.BitVec.extractLsb Xt 47 44)) with
    | 0b0000 => 12
    | 0b0001 => 14
    | 0b0010 => 16
    | 0b0011 => 21
    | 0b0100 => 25
    | 0b0101 => 29
    | 0b0110 => 30
    | 0b0111 => 34
    | 0b1000 => 36
    | 0b1001 => 39
    | _ => 0
  let w__3 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  let w__4 ← (( do (DecodePGS (_get_GPCCR_EL3_Type_PGS w__3)) ) : SailM PGSe )
  let p : Int :=
    match w__4 with
    | .PGS_4KB => 12
    | .PGS_16KB => 14
    | .PGS_64KB => 16
  let p : Int := p
  let range_bits : Int :=
    if ((range_bits <b p) : Bool)
    then p
    else range_bits
  let range_bits : Int := range_bits
  let BaseADDR : (BitVec 52) := (Zeros (n := 52))
  let w__5 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  let BaseADDR : (BitVec 52) :=
    match (BitVec.setWidth 2 (_get_GPCCR_EL3_Type_PGS w__5)) with
    | 0b00 => (Sail.BitVec.updateSubrange BaseADDR 51 12 (Sail.BitVec.extractLsb Xt 39 0))
    | 0b10 => (Sail.BitVec.updateSubrange BaseADDR 51 14 (Sail.BitVec.extractLsb Xt 39 2))
    | 0b01 => (Sail.BitVec.updateSubrange BaseADDR 51 16 (Sail.BitVec.extractLsb Xt 39 4))
    | _ => BaseADDR
  ArmFull.assert (range_bits ≥b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36576.39-36576.40"
  ArmFull.assert (52 ≥b range_bits) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36577.40-36577.41"
  let start_addr : (BitVec 52) :=
    (BaseADDR &&& (Sail.BitVec.castWidth (m := 52) (Complement.complement
        (Sail.BitVec.zeroExtend (Ones (n := (Sail.Int.toNatChecked (range_bits)))) 52))))
  let end_addr_name : (BitVec 52) :=
    (start_addr + (Sail.BitVec.castWidth (m := 52) (Sail.BitVec.zeroExtend
        (Ones (n := (Sail.Int.toNatChecked (range_bits)))) 52)))
  let r : TLBIRecord := { r with address := (Sail.BitVec.zeroExtend start_addr 64) }
  let r : TLBIRecord := { r with end_address_name := (Sail.BitVec.zeroExtend end_addr_name 64) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch64_TLBI_PAALL (shareability : Shareability) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         (HaveRME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL3) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__2 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36592.39-36592.40"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2486) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_PAALL }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := TLBI_AllAttr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch32_GetVARange (va : (BitVec 32)) (t0sz : (BitVec 3)) (t1sz : (BitVec 3)) : SailM VARange := do
  let lo_iasize : Int := (AArch32_S1IASize t0sz)
  let up_iasize : Int := (AArch32_S1IASize t1sz)
  if (((t1sz == 0b000#3) && (t0sz == 0b000#3)) : Bool)
  then (pure (VARange_LOWER))
  else
    (do
      if ((t1sz == 0b000#3) : Bool)
      then
        (pure (if ((is_zero_subrange va 31 lo_iasize) : Bool)
          then VARange_LOWER
          else VARange_UPPER))
      else
        (do
          if ((t0sz == 0b000#3) : Bool)
          then
            (pure (if ((is_ones_subrange va 31 up_iasize) : Bool)
              then VARange_UPPER
              else VARange_LOWER))
          else
            (do
              if ((is_zero_subrange va 31 lo_iasize) : Bool)
              then (pure (VARange_LOWER))
              else
                (do
                  if ((is_ones_subrange va 31 up_iasize) : Bool)
                  then (pure (VARange_UPPER))
                  else
                    (do
                      (__UNKNOWN_VARange ()))))))


def AArch32_S1TTWParamsEL2 (_ : Unit) : SailM S1TTWParams := do
  let walkparams ← (( do (undefined_S1TTWParams (← occLabel 2505) ()) ) : SailM S1TTWParams )
  let walkparams : S1TTWParams := { walkparams with tgx := TGx_4KB }
  let w__0 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with t0sz := (_get_HTCR_Type_T0SZ w__0) } : S1TTWParams)
  let w__1 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with irgn := (_get_HTCR_Type_SH0 w__1) } : S1TTWParams)
  let w__2 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with orgn := (_get_HTCR_Type_IRGN0 w__2) } : S1TTWParams)
  let w__3 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with sh := (_get_HTCR_Type_ORGN0 w__3) } : S1TTWParams)
  let w__4 ← (( do (AArch32_HaveHPDExt ()) ) : SailM Bool )
  let w__6 ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
        (pure ((_get_HTCR_Type_HPD w__5))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hpd := w__6 } : S1TTWParams)
  let w__7 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with ee := (_get_HSCTLR_Type_EE w__7) } : S1TTWParams)
  let w__8 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with wxn := (_get_HSCTLR_Type_WXN w__8) } : S1TTWParams)
  let w__9 ← (( do (HaveTrapLoadStoreMultipleDeviceExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__9 : Bool)
    then
      (do
        let w__10 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
        let walkparams :=
          ({ walkparams with ntlsmd := (_get_HSCTLR_Type_nTLSMD w__10) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with ntlsmd := 1#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__11 ← (( do (HMAIR1_read ()) ) : SailM (BitVec 32) )
  let w__12 ← (( do (HMAIR0_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with mair := (Mk_MAIRType (w__11 +++ w__12)) } : S1TTWParams)
  (pure (walkparams))


def AArch32_S1LDHasPermissionsFault (regime : Regime) (walkparams : S1TTWParams) (perms : Permissions) (memtype : MemType) (paspace : PASpace) (accdesc : AccessDescriptor) : SailM Bool := do
  let constraint_name ← (( do (undefined_Constraint (← occLabel 2514) ()) ) : SailM Constraint )
  let pan ← (( do (undefined_bitvector_at (← occLabel 2515) 1) ) : SailM (BitVec 1) )
  let px ← (( do (undefined_bitvector_at (← occLabel 2516) 1) ) : SailM (BitVec 1) )
  let pxn ← (( do (undefined_bitvector_at (← occLabel 2517) 1) ) : SailM (BitVec 1) )
  let ux ← (( do (undefined_bitvector_at (← occLabel 2518) 1) ) : SailM (BitVec 1) )
  let r ← (( do (undefined_bitvector_at (← occLabel 2519) 1) ) : SailM (BitVec 1) )
  let w ← (( do (undefined_bitvector_at (← occLabel 2520) 1) ) : SailM (BitVec 1) )
  let x ← (( do (undefined_bitvector_at (← occLabel 2521) 1) ) : SailM (BitVec 1) )
  let pr ← (( do (undefined_bitvector_at (← occLabel 2522) 1) ) : SailM (BitVec 1) )
  let pw ← (( do (undefined_bitvector_at (← occLabel 2523) 1) ) : SailM (BitVec 1) )
  let ur ← (( do (undefined_bitvector_at (← occLabel 2524) 1) ) : SailM (BitVec 1) )
  let uw ← (( do (undefined_bitvector_at (← occLabel 2525) 1) ) : SailM (BitVec 1) )
  let xn ← (( do (undefined_bitvector_at (← occLabel 2526) 1) ) : SailM (BitVec 1) )
  let (r, w, x) ← (( do
    if ((HasUnprivileged regime) : Bool)
    then
      (do
        let (pr, pw, ur, uw) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
          match (BitVec.setWidth 2 (Sail.BitVec.extractLsb perms.ap 2 1)) with
          | 0b00 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b01 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 1#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b10 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | _ =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
        let (pr, pw, ur, uw) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
          match perms.ap_table with
          | 0b00 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((pr, pw, ur, uw) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b01 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((pr, pw, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b10 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((pr, 0#1, ur, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | _ =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((pr, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
        let xn : (BitVec 1) := (perms.xn ||| perms.xn_table)
        let pxn : (BitVec 1) := (perms.pxn ||| perms.pxn_table)
        let ux : (BitVec 1) := (ur &&& (Complement.complement (xn ||| (uw &&& walkparams.wxn))))
        let px : (BitVec 1) :=
          (pr &&& (Complement.complement
              (((xn ||| pxn) ||| (pw &&& walkparams.wxn)) ||| (uw &&& walkparams.uwxn))))
        let w__1 ← (( do
          (pure ((← do
                (HavePANExt ())) && (accdesc.pan : Bool))) ) : SailM Bool )
        let (pr, pw) ← (( do
          if (w__1 : Bool)
          then
            (do
              let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
              let pan : (BitVec 1) := (w__2.PAN &&& (ur ||| uw))
              let pr : (BitVec 1) := (pr &&& (Complement.complement pan))
              let pw : (BitVec 1) := (pw &&& (Complement.complement pan))
              (pure ((pr, pw))))
          else (pure ((pr, pw))) ) : SailM ((BitVec 1) × (BitVec 1)) )
        let (tup__0, tup__1, tup__2) :=
          (if ((accdesc.el == EL0) : Bool)
          then (ur, uw, ux)
          else (pr, pw, px) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
        let r : (BitVec 1) := tup__0
        let w : (BitVec 1) := tup__1
        let x : (BitVec 1) := tup__2
        let x : (BitVec 1) :=
          if (((BEq.beq accdesc.ss SS_Secure) && (BEq.beq paspace PAS_NonSecure)) : Bool)
          then (x &&& (Complement.complement walkparams.sif))
          else x
        (pure ((r, w, x))))
    else
      (let (r, w) : ((BitVec 1) × (BitVec 1)) :=
        match (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access perms.ap 2)])) with
        | 0 =>
          (let (tup__0, tup__1) := ((1#1, 1#1) : ((BitVec 1) × (BitVec 1)))
          let r : (BitVec 1) := tup__0
          let w : (BitVec 1) := tup__1
          (r, w))
        | _ =>
          (let (tup__0, tup__1) := ((1#1, 0#1) : ((BitVec 1) × (BitVec 1)))
          let r : (BitVec 1) := tup__0
          let w : (BitVec 1) := tup__1
          (r, w))
      let (r, w) : ((BitVec 1) × (BitVec 1)) :=
        match (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access perms.ap_table 1)])) with
        | 0 =>
          (let (tup__0, tup__1) := ((r, w) : ((BitVec 1) × (BitVec 1)))
          let r : (BitVec 1) := tup__0
          let w : (BitVec 1) := tup__1
          (r, w))
        | _ =>
          (let (tup__0, tup__1) := ((r, 0#1) : ((BitVec 1) × (BitVec 1)))
          let r : (BitVec 1) := tup__0
          let w : (BitVec 1) := tup__1
          (r, w))
      let xn : (BitVec 1) := (perms.xn ||| perms.xn_table)
      let x : (BitVec 1) := (Complement.complement (xn ||| (w &&& walkparams.wxn)))
      (pure ((r, w, x)))) ) : SailM ((BitVec 1) × (BitVec 1) × (BitVec 1)) )
  if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
  then
    (do
      let constraint_name ← (( do (ConstrainUnpredictable Unpredictable_INSTRDEVICE) ) : SailM
        Constraint )
      (pure (if (((BEq.beq constraint_name Constraint_FAULT) && (BEq.beq memtype MemType_Device)) : Bool)
        then true
        else (x == 0#1))))
  else
    (pure (if (((BEq.beq accdesc.acctype AccessType_IC) || (BEq.beq accdesc.acctype AccessType_DC)) : Bool)
      then false
      else
        (if (accdesc.write : Bool)
        then (w == 0#1)
        else (r == 0#1))))


end ArmFull.Functions
