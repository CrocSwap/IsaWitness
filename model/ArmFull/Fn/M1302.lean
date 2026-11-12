import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0117
import ArmFull.Fn.M1184
import ArmFull.Fn.M1185

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

def decode_stlxrb_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
              c Constraint_NOP))) "sail-arm/instrs64.sail:30064.84-30064.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
                    c Constraint_NOP))) "sail-arm/instrs64.sail:30081.88-30081.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure (rt_unknown)))
              | _ => (pure (rt_unknown)))
          else (pure (rt_unknown)) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
                    c Constraint_NOP))) "sail-arm/instrs64.sail:30097.88-30097.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure (rn_unknown)))
              | _ => (pure (rn_unknown)))
          else (pure (rn_unknown)) ) : SailM Bool )
        (pure ((rn_unknown, rt_unknown))))
    else (pure ((rn_unknown, rt_unknown))) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elsize)) memop (Sail.Int.toNatChecked (n)) pair regsize rn_unknown
    rt_unknown (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))
    tagchecked)


def decode_stlxrh_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
              c Constraint_NOP))) "sail-arm/instrs64.sail:30150.84-30150.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
                    c Constraint_NOP))) "sail-arm/instrs64.sail:30167.88-30167.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure (rt_unknown)))
              | _ => (pure (rt_unknown)))
          else (pure (rt_unknown)) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
                    c Constraint_NOP))) "sail-arm/instrs64.sail:30183.88-30183.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure (rn_unknown)))
              | _ => (pure (rn_unknown)))
          else (pure (rn_unknown)) ) : SailM Bool )
        (pure ((rn_unknown, rt_unknown))))
    else (pure ((rn_unknown, rt_unknown))) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elsize)) memop (Sail.Int.toNatChecked (n)) pair regsize rn_unknown
    rt_unknown (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))
    tagchecked)


def decode_stxr_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
              c Constraint_NOP))) "sail-arm/instrs64.sail:30236.84-30236.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
                    c Constraint_NOP))) "sail-arm/instrs64.sail:30253.88-30253.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure (rt_unknown)))
              | _ => (pure (rt_unknown)))
          else (pure (rt_unknown)) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
                    c Constraint_NOP))) "sail-arm/instrs64.sail:30269.88-30269.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure (rn_unknown)))
              | _ => (pure (rn_unknown)))
          else (pure (rn_unknown)) ) : SailM Bool )
        (pure ((rn_unknown, rt_unknown))))
    else (pure ((rn_unknown, rt_unknown))) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elsize)) memop (Sail.Int.toNatChecked (n)) pair regsize rn_unknown
    rt_unknown (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))
    tagchecked)


def decode_stxrb_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
              c Constraint_NOP))) "sail-arm/instrs64.sail:30322.84-30322.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
                    c Constraint_NOP))) "sail-arm/instrs64.sail:30339.88-30339.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure (rt_unknown)))
              | _ => (pure (rt_unknown)))
          else (pure (rt_unknown)) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
                    c Constraint_NOP))) "sail-arm/instrs64.sail:30355.88-30355.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure (rn_unknown)))
              | _ => (pure (rn_unknown)))
          else (pure (rn_unknown)) ) : SailM Bool )
        (pure ((rn_unknown, rt_unknown))))
    else (pure ((rn_unknown, rt_unknown))) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elsize)) memop (Sail.Int.toNatChecked (n)) pair regsize rn_unknown
    rt_unknown (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))
    tagchecked)


def decode_stxrh_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
              c Constraint_NOP))) "sail-arm/instrs64.sail:30408.84-30408.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
                    c Constraint_NOP))) "sail-arm/instrs64.sail:30425.88-30425.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure (rt_unknown)))
              | _ => (pure (rt_unknown)))
          else (pure (rt_unknown)) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
                    c Constraint_NOP))) "sail-arm/instrs64.sail:30441.88-30441.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure (rn_unknown)))
              | _ => (pure (rn_unknown)))
          else (pure (rn_unknown)) ) : SailM Bool )
        (pure ((rn_unknown, rt_unknown))))
    else (pure ((rn_unknown, rt_unknown))) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elsize)) memop (Sail.Int.toNatChecked (n)) pair regsize rn_unknown
    rt_unknown (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))
    tagchecked)


def decode_ldiapp_aarch64_instrs_memory_ordered_pair_ldiapp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc2 : (BitVec 4)) (Rt2 : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let postindex : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 0)])) == 0#1)
  let wback : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 0)])) == 0#1)
  let offset ← (( do (undefined_int_at (← occLabel 4445) ()) ) : SailM Int )
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let scale : Int :=
    (2 +i (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)]))))
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let memop ← (( do (undefined_MemOp (← occLabel 4446) ()) ) : SailM MemOp )
  let (memop, offset) : (MemOp × Int) :=
    if ((L == 1#1) : Bool)
    then
      (let memop : MemOp := MemOp_LOAD
      let offset : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 0)])) == 0#1) : Bool)
        then (Int.shiftl 2 (Sail.Int.toNatChecked (scale)))
        else 0
      (memop, offset))
    else
      (let memop : MemOp := MemOp_STORE
      let offset : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 0)])) == 0#1) : Bool)
        then ((Neg.neg 1) *i (Int.shiftl 2 (Sail.Int.toNatChecked (scale))))
        else 0
      (memop, offset))
  let offset : Int := offset
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-arm/instrs64.sail:30759.113-30759.114"
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
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-arm/instrs64.sail:30778.107-30778.108"
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
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
              c Constraint_NOP))) "sail-arm/instrs64.sail:30797.84-30797.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "sail-arm/instrs64.sail:30811.44-30811.45"
  (execute_aarch64_instrs_memory_ordered_pair_ldiapp (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wb_unknown wback)


def decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let nontemporal : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let scale : Int :=
    (2 +i (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)]))))
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
              c Constraint_NOP))) "sail-arm/instrs64.sail:30921.84-30921.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "sail-arm/instrs64.sail:30935.44-30935.45"
  (execute_aarch64_instrs_memory_pair_general_no_alloc (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wback)


def decode_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let nontemporal : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let scale : Int :=
    (2 +i (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)]))))
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
              c Constraint_NOP))) "sail-arm/instrs64.sail:30970.84-30970.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "sail-arm/instrs64.sail:30984.44-30984.45"
  (execute_aarch64_instrs_memory_pair_general_no_alloc (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wback)


def decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let nontemporal : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((opc == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let scale : Int := (2 +i (BitVec.toNat opc))
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
              c Constraint_NOP))) "sail-arm/instrs64.sail:31076.84-31076.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "sail-arm/instrs64.sail:31090.54-31090.55"
  (execute_aarch64_instrs_memory_pair_simdfp_no_alloc (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wback)


end ArmFull.Functions
