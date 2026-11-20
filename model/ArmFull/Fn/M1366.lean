module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M1246 set_option backward.proofsInPublic true @[expose] public section

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

def decode_ldxrb_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29806.84-29806.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | .Constraint_NOP =>
          (do
            (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29823.88-29823.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29839.88-29839.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
                  (EndOfInstruction ())
                  (pure (rn_unknown)))
              | _ => (pure (rn_unknown)))
          else (pure (rn_unknown)) ) : SailM Bool )
        (pure ((rn_unknown, rt_unknown))))
    else (pure ((rn_unknown, rt_unknown))) ) : SailM (Bool × Bool) )
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_exclusive_single acqrel (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elsize)) memop (Sail.Int.toNatChecked (n)) pair regsize rn_unknown
    rt_unknown (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))
    tagchecked)


def decode_ldxrh_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29892.84-29892.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | .Constraint_NOP =>
          (do
            (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29909.88-29909.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29925.88-29925.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
                  (EndOfInstruction ())
                  (pure (rn_unknown)))
              | _ => (pure (rn_unknown)))
          else (pure (rn_unknown)) ) : SailM Bool )
        (pure ((rn_unknown, rt_unknown))))
    else (pure ((rn_unknown, rt_unknown))) ) : SailM (Bool × Bool) )
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_exclusive_single acqrel (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elsize)) memop (Sail.Int.toNatChecked (n)) pair regsize rn_unknown
    rt_unknown (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))
    tagchecked)


def decode_stlxr_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29978.84-29978.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | .Constraint_NOP =>
          (do
            (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29995.88-29995.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30011.88-30011.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
                  (EndOfInstruction ())
                  (pure (rn_unknown)))
              | _ => (pure (rn_unknown)))
          else (pure (rn_unknown)) ) : SailM Bool )
        (pure ((rn_unknown, rt_unknown))))
    else (pure ((rn_unknown, rt_unknown))) ) : SailM (Bool × Bool) )
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_exclusive_single acqrel (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elsize)) memop (Sail.Int.toNatChecked (n)) pair regsize rn_unknown
    rt_unknown (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))
    tagchecked)


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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30064.84-30064.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | .Constraint_NOP =>
          (do
            (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30081.88-30081.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30097.88-30097.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
                  (EndOfInstruction ())
                  (pure (rn_unknown)))
              | _ => (pure (rn_unknown)))
          else (pure (rn_unknown)) ) : SailM Bool )
        (pure ((rn_unknown, rt_unknown))))
    else (pure ((rn_unknown, rt_unknown))) ) : SailM (Bool × Bool) )
  (__ArmCertEndOfDecode ())
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30150.84-30150.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | .Constraint_NOP =>
          (do
            (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30167.88-30167.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30183.88-30183.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
                  (EndOfInstruction ())
                  (pure (rn_unknown)))
              | _ => (pure (rn_unknown)))
          else (pure (rn_unknown)) ) : SailM Bool )
        (pure ((rn_unknown, rt_unknown))))
    else (pure ((rn_unknown, rt_unknown))) ) : SailM (Bool × Bool) )
  (__ArmCertEndOfDecode ())
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30236.84-30236.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | .Constraint_NOP =>
          (do
            (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30253.88-30253.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30269.88-30269.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
                  (EndOfInstruction ())
                  (pure (rn_unknown)))
              | _ => (pure (rn_unknown)))
          else (pure (rn_unknown)) ) : SailM Bool )
        (pure ((rn_unknown, rt_unknown))))
    else (pure ((rn_unknown, rt_unknown))) ) : SailM (Bool × Bool) )
  (__ArmCertEndOfDecode ())
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30322.84-30322.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | .Constraint_NOP =>
          (do
            (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30339.88-30339.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:30355.88-30355.89"
              match c with
              | .Constraint_UNKNOWN => (pure (true))
              | .Constraint_UNDEF =>
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              | .Constraint_NOP =>
                (do
                  (__ArmCertEndOfDecode ())
                  (EndOfInstruction ())
                  (pure (rn_unknown)))
              | _ => (pure (rn_unknown)))
          else (pure (rn_unknown)) ) : SailM Bool )
        (pure ((rn_unknown, rt_unknown))))
    else (pure ((rn_unknown, rt_unknown))) ) : SailM (Bool × Bool) )
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_exclusive_single acqrel (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elsize)) memop (Sail.Int.toNatChecked (n)) pair regsize rn_unknown
    rt_unknown (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))
    tagchecked)


end ArmFull.Functions
