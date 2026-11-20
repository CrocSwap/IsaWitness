module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0226
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1129 set_option backward.proofsInPublic true @[expose] public section

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

def decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int := esize
      let elements : Nat := 1
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int := esize
      let elements : Nat := 1
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int := esize
      let elements : Nat := 1
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int := esize
      let elements : Nat := 1
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int := esize
      let elements : Nat := 1
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int := esize
      let elements : Nat := 1
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (n)) rounding is_unsigned))


def decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, part : Nat, List.elem
  part [0, 1] ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_float_narrow (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4243)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (FPConvert__1 w__0 w__1 esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (Vpart_set d part datasize (Sail.BitVec.castWidth result))


def decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((sz == 0#1) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 32
      let datasize : Int := esize
      let elements : Nat := 1
      let part : Nat := 0
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (n)) part))


def decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((sz == 0#1) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 32
      let datasize : Nat := 64
      let elements : Nat := 2
      let part : Int := (BitVec.toNat Q)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd (Sail.Int.toNatChecked (d))
        datasize elements esize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))))


def decode_fcvtzs_float_fix_aarch64_instrs_float_convert_fix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4246) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4247) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4248) ()) ) : SailM Bool )
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ())))
    | _ =>
      (do
        let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        if (w__0 : Bool)
        then (pure (16))
        else
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let fltsize : Int := fltsize
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access scale 5)])) == 0#1)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let fracbits : Int := (64 -i (BitVec.toNat scale))
      let (is_unsigned, op, rounding) ← (( do
        match (BitVec.setWidth 4 ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) with
        | 0b0011 =>
          (let rounding : FPRounding := FPRounding_ZERO
          let is_unsigned : Bool :=
            ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure ((is_unsigned, op, rounding))))
        | 0b0100 =>
          (do
            let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__2 ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
            let rounding := (w__2 : FPRounding)
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_ItoF
            (pure ((is_unsigned, op, rounding))))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ()))) ) : SailM (Bool × FPConvOp × FPRounding) )
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_float_convert_fix (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (fltsize)) (Sail.Int.toNatChecked (fracbits))
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op rounding is_unsigned))


end ArmFull.Functions
