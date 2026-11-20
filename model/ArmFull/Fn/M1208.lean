module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M1158
public import ArmFull.Fn.M1161 set_option backward.proofsInPublic true @[expose] public section

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

def decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := 16
  let esize ← (( do
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
  let esize : Int := esize
  let negated : Bool := (op == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_float_arithmetic_mul_product (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) negated)


def decode_fnmul_float_aarch64_instrs_float_arithmetic_mul_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := 16
  let esize ← (( do
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
  let esize : Int := esize
  let negated : Bool := (op == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_float_arithmetic_mul_product (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) negated)


def decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let idxdsize : Int :=
        if ((H == 1#1) : Bool)
        then 128
        else 64
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Rd)
      let index : Int := (BitVec.toNat ((H +++ L) +++ M))
      let esize : Nat := 16
      let datasize : Int := esize
      let elements : Nat := 1
      let mulx_op : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) mulx_op (Sail.Int.toNatChecked (n))))


def decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4290) 0 3))) ) :
    SailM Nat )
  let Rmhi : (BitVec 1) := M
  let b__0 := (sz +++ L)
  let index ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
    then
      (let index : Nat := (BitVec.toNat (H +++ L))
      (pure (index)))
    else
      (do
        match b__0 with
        | 0b10 =>
          (let index : Nat := (BitVec.toNat H)
          (pure (index)))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Nat )
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let mulx_op : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    mulx_op (Sail.Int.toNatChecked (n)))


def decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let idxdsize : Int :=
        if ((H == 1#1) : Bool)
        then 128
        else 64
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Rd)
      let index : Int := (BitVec.toNat ((H +++ L) +++ M))
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      let mulx_op : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) mulx_op (Sail.Int.toNatChecked (n))))


def decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4291) 0 3))) ) :
    SailM Nat )
  let Rmhi : (BitVec 1) := M
  let b__0 := (sz +++ L)
  let index ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
    then
      (let index : Nat := (BitVec.toNat (H +++ L))
      (pure (index)))
    else
      (do
        match b__0 with
        | 0b10 =>
          (let index : Nat := (BitVec.toNat H)
          (pure (index)))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Nat )
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
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
      let mulx_op : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (idxdsize))
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) mulx_op
        (Sail.Int.toNatChecked (n))))


def decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let idxdsize : Int :=
        if ((H == 1#1) : Bool)
        then 128
        else 64
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Rd)
      let index : Int := (BitVec.toNat ((H +++ L) +++ M))
      let esize : Nat := 16
      let datasize : Int := esize
      let elements : Nat := 1
      let mulx_op : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) mulx_op (Sail.Int.toNatChecked (n))))


def decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4292) 0 3))) ) :
    SailM Nat )
  let Rmhi : (BitVec 1) := M
  let b__0 := (sz +++ L)
  let index ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
    then
      (let index : Nat := (BitVec.toNat (H +++ L))
      (pure (index)))
    else
      (do
        match b__0 with
        | 0b10 =>
          (let index : Nat := (BitVec.toNat H)
          (pure (index)))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Nat )
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let mulx_op : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    mulx_op (Sail.Int.toNatChecked (n)))


def decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let idxdsize : Int :=
        if ((H == 1#1) : Bool)
        then 128
        else 64
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Rd)
      let index : Int := (BitVec.toNat ((H +++ L) +++ M))
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      let mulx_op : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) mulx_op (Sail.Int.toNatChecked (n))))


def decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4293) 0 3))) ) :
    SailM Nat )
  let Rmhi : (BitVec 1) := M
  let b__0 := (sz +++ L)
  let index ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
    then
      (let index : Nat := (BitVec.toNat (H +++ L))
      (pure (index)))
    else
      (do
        match b__0 with
        | 0b10 =>
          (let index : Nat := (BitVec.toNat H)
          (pure (index)))
        | _ =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))) ) : SailM Nat )
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
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
      let mulx_op : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (idxdsize))
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) mulx_op
        (Sail.Int.toNatChecked (n))))


def decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
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
      let m : Int := (BitVec.toNat Rm)
      let esize : Nat := 16
      let datasize : Int := esize
      let elements : Nat := 1
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
      let m : Int := (BitVec.toNat Rm)
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
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
      let m : Int := (BitVec.toNat Rm)
      let esize : Nat := 16
      let datasize : Int := esize
      let elements : Nat := 1
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
      let m : Int := (BitVec.toNat Rm)
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
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
      let m : Int := (BitVec.toNat Rm)
      let esize : Nat := 16
      let datasize : Int := esize
      let elements : Nat := 1
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
      let m : Int := (BitVec.toNat Rm)
      let esize : Nat := 16
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (n))))


end ArmFull.Functions
