import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0018
import ArmFull.Fn.M0117
import ArmFull.Fn.M1183
import ArmFull.Fn.M1184

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

def decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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


def decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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


def decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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


def decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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


def decode_ldap1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let index ← (( do (undefined_int_at (← occLabel 4395) ()) ) : SailM Int )
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
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:27226.48-27226.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb_ordered (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_stl1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let index ← (( do (undefined_int_at (← occLabel 4396) ()) ) : SailM Int )
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
  ArmFull.assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:27295.48-27295.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb_ordered (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (esize)) index m memop (Sail.Int.toNatChecked (n)) replicate
    (Sail.Int.toNatChecked (selem)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ldapr_aarch64_instrs_memory_ordered_rcpc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let offset : Nat := 0
  let wb_unknown : Bool := false
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let s : Int := (BitVec.toNat Rs)
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered_rcpc (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (n)) offset regsize (Sail.Int.toNatChecked (t)) tagchecked wb_unknown
    wback)


def decode_ldapr_aarch64_instrs_memory_ordered_rcpc_writeback (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let regsize : Int :=
    if ((size == 0b11#2) : Bool)
    then 64
    else 32
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let offset : Int := (Int.shiftl 1 (BitVec.toNat size))
  let tagchecked : Bool := (wback || (n != 31))
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((wback && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-arm/instrs64.sail:27393.113-27393.114"
        match c with
        | .Constraint_WBSUPPRESS =>
          (let wback : Bool := false
          (pure ((wb_unknown, wback))))
        | .Constraint_UNKNOWN =>
          (let wb_unknown : Bool := true
          (pure ((wb_unknown, wback))))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure ((wb_unknown, wback))))
        | _ => (pure ((wb_unknown, wback))))
    else (pure ((wb_unknown, wback))) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_ordered_rcpc (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (regsize))
    (Sail.Int.toNatChecked (t)) tagchecked wb_unknown wback)


def decode_ldaprb_aarch64_instrs_memory_ordered_rcpc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let offset : Nat := 0
  let wb_unknown : Bool := false
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let s : Int := (BitVec.toNat Rs)
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered_rcpc (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (n)) offset regsize (Sail.Int.toNatChecked (t)) tagchecked wb_unknown
    wback)


def decode_ldaprh_aarch64_instrs_memory_ordered_rcpc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let offset : Nat := 0
  let wb_unknown : Bool := false
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let s : Int := (BitVec.toNat Rs)
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered_rcpc (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (n)) offset regsize (Sail.Int.toNatChecked (t)) tagchecked wb_unknown
    wback)


def decode_ldapur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let memop ← (( do (undefined_MemOp (← occLabel 4401) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4402) ()) ) : SailM Bool )
  let regsize : Int := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure ((is_signed, memop, regsize))))
    else
      (do
        if ((size == 0b11#2) : Bool)
        then sailThrow ((Error_Undefined ()))
        else
          (do
            let memop : MemOp := MemOp_LOAD
            if (((size == 0b10#2) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1)) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let regsize : Int :=
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
              then 32
              else 64
            let is_signed : Bool := true
            (pure ((is_signed, memop, regsize))))) ) : SailM (Bool × MemOp × Int) )
  let regsize : Int := regsize
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint (← occLabel 4403) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-arm/instrs64.sail:27586.113-27586.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure ((wb_unknown, wback))))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure ((wb_unknown, wback))))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure ((wb_unknown, wback))))
          | _ => (pure ((wb_unknown, wback))) ) : SailM (Bool × Bool) )
        (pure ((c, wb_unknown, wback))))
    else (pure ((c, wb_unknown, wback))) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-arm/instrs64.sail:27605.107-27605.108"
        match c with
        | .Constraint_NONE => (pure (false))
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) offset postindex
    (Sail.Int.toNatChecked (regsize)) rt_unknown is_signed (Sail.Int.toNatChecked (t)) tagchecked
    wb_unknown wback)


def decode_ldapurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let memop ← (( do (undefined_MemOp (← occLabel 4404) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4405) ()) ) : SailM Bool )
  let regsize : Int := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure ((is_signed, memop, regsize))))
    else
      (do
        if ((size == 0b11#2) : Bool)
        then sailThrow ((Error_Undefined ()))
        else
          (do
            let memop : MemOp := MemOp_LOAD
            if (((size == 0b10#2) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1)) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let regsize : Int :=
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
              then 32
              else 64
            let is_signed : Bool := true
            (pure ((is_signed, memop, regsize))))) ) : SailM (Bool × MemOp × Int) )
  let regsize : Int := regsize
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint (← occLabel 4406) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-arm/instrs64.sail:27671.113-27671.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure ((wb_unknown, wback))))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure ((wb_unknown, wback))))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure ((wb_unknown, wback))))
          | _ => (pure ((wb_unknown, wback))) ) : SailM (Bool × Bool) )
        (pure ((c, wb_unknown, wback))))
    else (pure ((c, wb_unknown, wback))) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-arm/instrs64.sail:27690.107-27690.108"
        match c with
        | .Constraint_NONE => (pure (false))
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) offset postindex
    (Sail.Int.toNatChecked (regsize)) rt_unknown is_signed (Sail.Int.toNatChecked (t)) tagchecked
    wb_unknown wback)


end ArmFull.Functions
