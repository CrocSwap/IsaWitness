import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0018
import ArmFull.Fn.M0086
import ArmFull.Fn.M0116
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0178
import ArmFull.Fn.M1078

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

def decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  (execute_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16 (Sail.Int.toNatChecked (d))
    esize (Sail.Int.toNatChecked (n)))


def decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  (execute_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_frint32x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFrintExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let intsize : Int :=
    if ((op == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if ((U == 0#1) : Bool)
    then (pure (FPRounding_ZERO))
    else
      (do
        let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        (FPRoundingMode w__1)) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n))
    rounding)


def decode_frint32z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFrintExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let intsize : Int :=
    if ((op == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if ((U == 0#1) : Bool)
    then (pure (FPRounding_ZERO))
    else
      (do
        let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        (FPRoundingMode w__1)) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n))
    rounding)


def decode_frint64x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFrintExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let intsize : Int :=
    if ((op == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if ((U == 0#1) : Bool)
    then (pure (FPRounding_ZERO))
    else
      (do
        let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        (FPRoundingMode w__1)) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n))
    rounding)


def decode_frint64z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFrintExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let intsize : Int :=
    if ((op == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if ((U == 0#1) : Bool)
    then (pure (FPRounding_ZERO))
    else
      (do
        let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        (FPRoundingMode w__1)) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n))
    rounding)


def decode_frint32x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFrintExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := 32
  let esize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | b__0 => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let esize : Int := esize
  let intsize : Int :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 0)])) == 0#1) : Bool)
    then (pure (FPRounding_ZERO))
    else
      (do
        let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        (FPRoundingMode w__1)) ) : SailM FPRounding )
  (execute_aarch64_instrs_float_arithmetic_round_frint_32_64 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n))
    rounding)


def decode_frint32z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFrintExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := 32
  let esize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | b__0 => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let esize : Int := esize
  let intsize : Int :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 0)])) == 0#1) : Bool)
    then (pure (FPRounding_ZERO))
    else
      (do
        let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        (FPRoundingMode w__1)) ) : SailM FPRounding )
  (execute_aarch64_instrs_float_arithmetic_round_frint_32_64 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n))
    rounding)


def decode_frint64x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFrintExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := 32
  let esize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | b__0 => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let esize : Int := esize
  let intsize : Int :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 0)])) == 0#1) : Bool)
    then (pure (FPRounding_ZERO))
    else
      (do
        let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        (FPRoundingMode w__1)) ) : SailM FPRounding )
  (execute_aarch64_instrs_float_arithmetic_round_frint_32_64 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n))
    rounding)


def decode_frint64z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFrintExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := 32
  let esize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | b__0 => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let esize : Int := esize
  let intsize : Int :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 1)])) == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 0)])) == 0#1) : Bool)
    then (pure (FPRounding_ZERO))
    else
      (do
        let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        (FPRoundingMode w__1)) ) : SailM FPRounding )
  (execute_aarch64_instrs_float_arithmetic_round_frint_32_64 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n))
    rounding)


def decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding (← occLabel 4303) ()) ) : SailM FPRounding )
  let b__0 := ((U +++ o1) +++ o2)
  let (exact, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (0#1 : (BitVec 1))) : Bool)
    then
      (do
        let w__0 ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
        let rounding := (w__0 : FPRounding)
        (pure ((exact, rounding))))
    else
      (do
        match b__0 with
        | 0b100 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          (pure ((exact, rounding))))
        | 0b101 => sailThrow ((Error_Undefined ()))
        | 0b110 =>
          (do
            let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__2 ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
            let rounding := (w__2 : FPRounding)
            let exact : Bool := true
            (pure ((exact, rounding))))
        | _ =>
          (do
            let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__4 ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
            let rounding := (w__4 : FPRounding)
            (pure ((exact, rounding))))) ) : SailM (Bool × FPRounding) )
  let rounding := rounding
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize exact (Sail.Int.toNatChecked (n)) rounding)


def decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding (← occLabel 4304) ()) ) : SailM FPRounding )
  let b__0 := ((U +++ o1) +++ o2)
  let (exact, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (0#1 : (BitVec 1))) : Bool)
    then
      (do
        let w__0 ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
        let rounding := (w__0 : FPRounding)
        (pure ((exact, rounding))))
    else
      (do
        match b__0 with
        | 0b100 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          (pure ((exact, rounding))))
        | 0b101 => sailThrow ((Error_Undefined ()))
        | 0b110 =>
          (do
            let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__2 ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
            let rounding := (w__2 : FPRounding)
            let exact : Bool := true
            (pure ((exact, rounding))))
        | _ =>
          (do
            let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__4 ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
            let rounding := (w__4 : FPRounding)
            (pure ((exact, rounding))))) ) : SailM (Bool × FPRounding) )
  let rounding := rounding
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) exact
    (Sail.Int.toNatChecked (n)) rounding)


def decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding (← occLabel 4305) ()) ) : SailM FPRounding )
  let b__0 := ((U +++ o1) +++ o2)
  let (exact, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (0#1 : (BitVec 1))) : Bool)
    then
      (do
        let w__0 ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
        let rounding := (w__0 : FPRounding)
        (pure ((exact, rounding))))
    else
      (do
        match b__0 with
        | 0b100 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          (pure ((exact, rounding))))
        | 0b101 => sailThrow ((Error_Undefined ()))
        | 0b110 =>
          (do
            let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__2 ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
            let rounding := (w__2 : FPRounding)
            let exact : Bool := true
            (pure ((exact, rounding))))
        | _ =>
          (do
            let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__4 ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
            let rounding := (w__4 : FPRounding)
            (pure ((exact, rounding))))) ) : SailM (Bool × FPRounding) )
  let rounding := rounding
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize exact (Sail.Int.toNatChecked (n)) rounding)


def decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding (← occLabel 4306) ()) ) : SailM FPRounding )
  let b__0 := ((U +++ o1) +++ o2)
  let (exact, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (0#1 : (BitVec 1))) : Bool)
    then
      (do
        let w__0 ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
        let rounding := (w__0 : FPRounding)
        (pure ((exact, rounding))))
    else
      (do
        match b__0 with
        | 0b100 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          (pure ((exact, rounding))))
        | 0b101 => sailThrow ((Error_Undefined ()))
        | 0b110 =>
          (do
            let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__2 ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
            let rounding := (w__2 : FPRounding)
            let exact : Bool := true
            (pure ((exact, rounding))))
        | _ =>
          (do
            let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__4 ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
            let rounding := (w__4 : FPRounding)
            (pure ((exact, rounding))))) ) : SailM (Bool × FPRounding) )
  let rounding := rounding
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) exact
    (Sail.Int.toNatChecked (n)) rounding)


def decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding (← occLabel 4307) ()) ) : SailM FPRounding )
  let b__0 := ((U +++ o1) +++ o2)
  let (exact, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (0#1 : (BitVec 1))) : Bool)
    then
      (do
        let w__0 ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
        let rounding := (w__0 : FPRounding)
        (pure ((exact, rounding))))
    else
      (do
        match b__0 with
        | 0b100 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          (pure ((exact, rounding))))
        | 0b101 => sailThrow ((Error_Undefined ()))
        | 0b110 =>
          (do
            let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__2 ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
            let rounding := (w__2 : FPRounding)
            let exact : Bool := true
            (pure ((exact, rounding))))
        | _ =>
          (do
            let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__4 ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
            let rounding := (w__4 : FPRounding)
            (pure ((exact, rounding))))) ) : SailM (Bool × FPRounding) )
  let rounding := rounding
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize exact (Sail.Int.toNatChecked (n)) rounding)


def decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding (← occLabel 4308) ()) ) : SailM FPRounding )
  let b__0 := ((U +++ o1) +++ o2)
  let (exact, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (0#1 : (BitVec 1))) : Bool)
    then
      (do
        let w__0 ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
        let rounding := (w__0 : FPRounding)
        (pure ((exact, rounding))))
    else
      (do
        match b__0 with
        | 0b100 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          (pure ((exact, rounding))))
        | 0b101 => sailThrow ((Error_Undefined ()))
        | 0b110 =>
          (do
            let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__2 ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
            let rounding := (w__2 : FPRounding)
            let exact : Bool := true
            (pure ((exact, rounding))))
        | _ =>
          (do
            let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__4 ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
            let rounding := (w__4 : FPRounding)
            (pure ((exact, rounding))))) ) : SailM (Bool × FPRounding) )
  let rounding := rounding
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) exact
    (Sail.Int.toNatChecked (n)) rounding)


def decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding (← occLabel 4309) ()) ) : SailM FPRounding )
  let b__0 := ((U +++ o1) +++ o2)
  let (exact, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (0#1 : (BitVec 1))) : Bool)
    then
      (do
        let w__0 ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
        let rounding := (w__0 : FPRounding)
        (pure ((exact, rounding))))
    else
      (do
        match b__0 with
        | 0b100 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          (pure ((exact, rounding))))
        | 0b101 => sailThrow ((Error_Undefined ()))
        | 0b110 =>
          (do
            let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__2 ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
            let rounding := (w__2 : FPRounding)
            let exact : Bool := true
            (pure ((exact, rounding))))
        | _ =>
          (do
            let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__4 ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
            let rounding := (w__4 : FPRounding)
            (pure ((exact, rounding))))) ) : SailM (Bool × FPRounding) )
  let rounding := rounding
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize exact (Sail.Int.toNatChecked (n)) rounding)


def decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding (← occLabel 4310) ()) ) : SailM FPRounding )
  let b__0 := ((U +++ o1) +++ o2)
  let (exact, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (0#1 : (BitVec 1))) : Bool)
    then
      (do
        let w__0 ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
        let rounding := (w__0 : FPRounding)
        (pure ((exact, rounding))))
    else
      (do
        match b__0 with
        | 0b100 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          (pure ((exact, rounding))))
        | 0b101 => sailThrow ((Error_Undefined ()))
        | 0b110 =>
          (do
            let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__2 ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
            let rounding := (w__2 : FPRounding)
            let exact : Bool := true
            (pure ((exact, rounding))))
        | _ =>
          (do
            let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__4 ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
            let rounding := (w__4 : FPRounding)
            (pure ((exact, rounding))))) ) : SailM (Bool × FPRounding) )
  let rounding := rounding
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) exact
    (Sail.Int.toNatChecked (n)) rounding)


end ArmFull.Functions
