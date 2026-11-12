import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0086
import ArmFull.Fn.M0144
import ArmFull.Fn.M1183

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

def decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) != 0b01#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_simd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    op)


def decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_simd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (n)) op)


def decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((sz +++ Q) != 0b01#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_simd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    op)


def decode_gcsstr_aarch64_instrs_memory_gcs_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (HaveGCS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let is_gcssttr : Bool := (opc == 0b001#3)
  (execute_aarch64_instrs_memory_gcs_general_register is_gcssttr (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (t)))


def decode_gcssttr_aarch64_instrs_memory_gcs_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (HaveGCS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let is_gcssttr : Bool := (opc == 0b001#3)
  (execute_aarch64_instrs_memory_gcs_general_register is_gcssttr (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (t)))


def decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let m ← (( do (__UNKNOWN_integer ()) ) : SailM Int )
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem : Int :=
    ((BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int_at (← occLabel 4338) ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure ((index, replicate, scale))))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure ((index, replicate, scale))))
    | 1 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let index : Int :=
          (BitVec.toNat ((Q +++ S) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)]))))
        (pure ((index, replicate, scale))))
    | 2 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let (index, scale) ← (( do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure ((index, scale))))
          else
            (do
              if ((S == 1#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (()))
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure ((index, scale)))) ) : SailM (Int × Int) )
        (pure ((index, replicate, scale))))
    | _ => (pure ((index, replicate, scale))) ) : SailM (Int × Bool × Int) )
  let scale : Int := scale
  let index : Int := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize : Int := (_shl_int_general 8 scale)
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:22879.48-22879.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem : Int :=
    ((BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int_at (← occLabel 4339) ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure ((index, replicate, scale))))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure ((index, replicate, scale))))
    | 1 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let index : Int :=
          (BitVec.toNat ((Q +++ S) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)]))))
        (pure ((index, replicate, scale))))
    | 2 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let (index, scale) ← (( do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure ((index, scale))))
          else
            (do
              if ((S == 1#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (()))
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure ((index, scale)))) ) : SailM (Int × Int) )
        (pure ((index, replicate, scale))))
    | _ => (pure ((index, replicate, scale))) ) : SailM (Int × Bool × Int) )
  let scale : Int := scale
  let index : Int := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize : Int := (_shl_int_general 8 scale)
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:22949.48-22949.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let m ← (( do (__UNKNOWN_integer ()) ) : SailM Int )
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem : Int :=
    ((BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int_at (← occLabel 4340) ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure ((index, replicate, scale))))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure ((index, replicate, scale))))
    | 1 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let index : Int :=
          (BitVec.toNat ((Q +++ S) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)]))))
        (pure ((index, replicate, scale))))
    | 2 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let (index, scale) ← (( do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure ((index, scale))))
          else
            (do
              if ((S == 1#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (()))
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure ((index, scale)))) ) : SailM (Int × Int) )
        (pure ((index, replicate, scale))))
    | _ => (pure ((index, replicate, scale))) ) : SailM (Int × Bool × Int) )
  let scale : Int := scale
  let index : Int := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize : Int := (_shl_int_general 8 scale)
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:23019.48-23019.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem : Int :=
    ((BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int_at (← occLabel 4341) ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure ((index, replicate, scale))))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure ((index, replicate, scale))))
    | 1 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let index : Int :=
          (BitVec.toNat ((Q +++ S) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)]))))
        (pure ((index, replicate, scale))))
    | 2 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let (index, scale) ← (( do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure ((index, scale))))
          else
            (do
              if ((S == 1#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (()))
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure ((index, scale)))) ) : SailM (Int × Int) )
        (pure ((index, replicate, scale))))
    | _ => (pure ((index, replicate, scale))) ) : SailM (Int × Bool × Int) )
  let scale : Int := scale
  let index : Int := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize : Int := (_shl_int_general 8 scale)
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:23089.48-23089.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let m ← (( do (__UNKNOWN_integer ()) ) : SailM Int )
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem : Int :=
    ((BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int_at (← occLabel 4342) ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure ((index, replicate, scale))))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure ((index, replicate, scale))))
    | 1 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let index : Int :=
          (BitVec.toNat ((Q +++ S) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)]))))
        (pure ((index, replicate, scale))))
    | 2 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let (index, scale) ← (( do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure ((index, scale))))
          else
            (do
              if ((S == 1#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (()))
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure ((index, scale)))) ) : SailM (Int × Int) )
        (pure ((index, replicate, scale))))
    | _ => (pure ((index, replicate, scale))) ) : SailM (Int × Bool × Int) )
  let scale : Int := scale
  let index : Int := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize : Int := (_shl_int_general 8 scale)
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:23159.48-23159.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem : Int :=
    ((BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int_at (← occLabel 4343) ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure ((index, replicate, scale))))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure ((index, replicate, scale))))
    | 1 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let index : Int :=
          (BitVec.toNat ((Q +++ S) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)]))))
        (pure ((index, replicate, scale))))
    | 2 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let (index, scale) ← (( do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure ((index, scale))))
          else
            (do
              if ((S == 1#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (()))
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure ((index, scale)))) ) : SailM (Int × Int) )
        (pure ((index, replicate, scale))))
    | _ => (pure ((index, replicate, scale))) ) : SailM (Int × Bool × Int) )
  let scale : Int := scale
  let index : Int := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize : Int := (_shl_int_general 8 scale)
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:23229.48-23229.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let m ← (( do (__UNKNOWN_integer ()) ) : SailM Int )
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem : Int :=
    ((BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int_at (← occLabel 4344) ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure ((index, replicate, scale))))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure ((index, replicate, scale))))
    | 1 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let index : Int :=
          (BitVec.toNat ((Q +++ S) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)]))))
        (pure ((index, replicate, scale))))
    | 2 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let (index, scale) ← (( do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure ((index, scale))))
          else
            (do
              if ((S == 1#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (()))
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure ((index, scale)))) ) : SailM (Int × Int) )
        (pure ((index, replicate, scale))))
    | _ => (pure ((index, replicate, scale))) ) : SailM (Int × Bool × Int) )
  let scale : Int := scale
  let index : Int := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize : Int := (_shl_int_general 8 scale)
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:23299.48-23299.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem : Int :=
    ((BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int_at (← occLabel 4345) ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure ((index, replicate, scale))))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure ((index, replicate, scale))))
    | 1 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let index : Int :=
          (BitVec.toNat ((Q +++ S) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)]))))
        (pure ((index, replicate, scale))))
    | 2 =>
      (do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)])) == 1#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        let (index, scale) ← (( do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure ((index, scale))))
          else
            (do
              if ((S == 1#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (()))
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure ((index, scale)))) ) : SailM (Int × Int) )
        (pure ((index, replicate, scale))))
    | _ => (pure ((index, replicate, scale))) ) : SailM (Int × Bool × Int) )
  let scale : Int := scale
  let index : Int := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize : Int := (_shl_int_general 8 scale)
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:23369.48-23369.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


end ArmFull.Functions
