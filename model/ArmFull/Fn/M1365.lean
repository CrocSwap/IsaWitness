module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M1245
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

def decode_ldxp_aarch64_instrs_memory_exclusive_pair (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 32 (BitVec.toNat sz))
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29128.84-29128.85"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29145.88-29145.89"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29161.88-29161.89"
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
  (execute_aarch64_instrs_memory_exclusive_pair acqrel (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elsize)) memop (Sail.Int.toNatChecked (n)) pair regsize rn_unknown
    rt_unknown (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))
    tagchecked)


def decode_stlxp_aarch64_instrs_memory_exclusive_pair (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 32 (BitVec.toNat sz))
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29214.84-29214.85"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29231.88-29231.89"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29247.88-29247.89"
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
  (execute_aarch64_instrs_memory_exclusive_pair acqrel (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elsize)) memop (Sail.Int.toNatChecked (n)) pair regsize rn_unknown
    rt_unknown (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))
    tagchecked)


def decode_stxp_aarch64_instrs_memory_exclusive_pair (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 32 (BitVec.toNat sz))
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29296.84-29296.85"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29313.88-29313.89"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29329.88-29329.89"
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
  (execute_aarch64_instrs_memory_exclusive_pair acqrel (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elsize)) memop (Sail.Int.toNatChecked (n)) pair regsize rn_unknown
    rt_unknown (Sail.Int.toNatChecked (s)) (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2))
    tagchecked)


def decode_ldaxr_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29462.84-29462.85"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29479.88-29479.89"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29495.88-29495.89"
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


def decode_ldaxrb_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29548.84-29548.85"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29565.88-29565.89"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29581.88-29581.89"
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


def decode_ldaxrh_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29634.84-29634.85"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29651.88-29651.89"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29667.88-29667.89"
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


def decode_ldxr_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29720.84-29720.85"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29737.88-29737.89"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29753.88-29753.89"
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
