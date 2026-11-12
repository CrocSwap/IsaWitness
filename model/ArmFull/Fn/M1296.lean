import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
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

def decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let index ← (( do (undefined_int_at (← occLabel 4355) ()) ) : SailM Int )
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
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:24069.48-24069.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let index ← (( do (undefined_int_at (← occLabel 4356) ()) ) : SailM Int )
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
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:24139.48-24139.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let index ← (( do (undefined_int_at (← occLabel 4357) ()) ) : SailM Int )
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
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:24209.48-24209.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let index ← (( do (undefined_int_at (← occLabel 4358) ()) ) : SailM Int )
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
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:24279.48-24279.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let index ← (( do (undefined_int_at (← occLabel 4359) ()) ) : SailM Int )
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
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:24349.48-24349.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let index ← (( do (undefined_int_at (← occLabel 4360) ()) ) : SailM Int )
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
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:24419.48-24419.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let index ← (( do (undefined_int_at (← occLabel 4361) ()) ) : SailM Int )
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
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:24489.48-24489.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) nontemporal replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let m ← (( do (__UNKNOWN_integer ()) ) : SailM Int )
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let rpt : Int := 1
  let selem : Int := 1
  let (rpt, selem) ← (( do
    match opcode with
    | 0b0000 =>
      (let rpt : Int := 1
      let selem : Int := 4
      (pure ((rpt, selem))))
    | 0b0010 =>
      (let rpt : Int := 4
      let selem : Int := 1
      (pure ((rpt, selem))))
    | 0b0100 =>
      (let rpt : Int := 1
      let selem : Int := 3
      (pure ((rpt, selem))))
    | 0b0110 =>
      (let rpt : Int := 3
      let selem : Int := 1
      (pure ((rpt, selem))))
    | 0b0111 =>
      (let rpt : Int := 1
      let selem : Int := 1
      (pure ((rpt, selem))))
    | 0b1000 =>
      (let rpt : Int := 1
      let selem : Int := 2
      (pure ((rpt, selem))))
    | 0b1010 =>
      (let rpt : Int := 2
      let selem : Int := 1
      (pure ((rpt, selem))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem : Int := selem
  let rpt : Int := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_memory_vector_multiple_no_wb (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) m memop (Sail.Int.toNatChecked (n)) nontemporal
    (Sail.Int.toNatChecked (rpt)) (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t))
    tagchecked wback)


def decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let rpt : Int := 1
  let selem : Int := 1
  let (rpt, selem) ← (( do
    match opcode with
    | 0b0000 =>
      (let rpt : Int := 1
      let selem : Int := 4
      (pure ((rpt, selem))))
    | 0b0010 =>
      (let rpt : Int := 4
      let selem : Int := 1
      (pure ((rpt, selem))))
    | 0b0100 =>
      (let rpt : Int := 1
      let selem : Int := 3
      (pure ((rpt, selem))))
    | 0b0110 =>
      (let rpt : Int := 3
      let selem : Int := 1
      (pure ((rpt, selem))))
    | 0b0111 =>
      (let rpt : Int := 1
      let selem : Int := 1
      (pure ((rpt, selem))))
    | 0b1000 =>
      (let rpt : Int := 1
      let selem : Int := 2
      (pure ((rpt, selem))))
    | 0b1010 =>
      (let rpt : Int := 2
      let selem : Int := 1
      (pure ((rpt, selem))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem : Int := selem
  let rpt : Int := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_memory_vector_multiple_no_wb (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) m memop (Sail.Int.toNatChecked (n)) nontemporal
    (Sail.Int.toNatChecked (rpt)) (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t))
    tagchecked wback)


end ArmFull.Functions
