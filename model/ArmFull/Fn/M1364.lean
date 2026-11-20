module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M1245 set_option backward.proofsInPublic true @[expose] public section

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

def decode_stlurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let memop ← (( do (undefined_MemOp (← occLabel 4425) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4426) ()) ) : SailM Bool )
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
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else
          (do
            let memop : MemOp := MemOp_LOAD
            let (is_signed, regsize) ← (( do
              if (((size == 0b10#2) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1)) : Bool)
              then
                (do
                  (__ArmCertEndOfDecode ())
                  sailThrow ((Error_Undefined ())))
              else
                (let regsize : Int :=
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
                  then 32
                  else 64
                let is_signed : Bool := true
                (pure ((is_signed, regsize)))) ) : SailM (Bool × Int) )
            (pure ((is_signed, memop, regsize))))) ) : SailM (Bool × MemOp × Int) )
  let regsize : Int := regsize
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint (← occLabel 4427) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-inputs/15-instrs64.sail:28266.113-28266.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure ((wb_unknown, wback))))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure ((wb_unknown, wback))))
          | .Constraint_UNDEF =>
            (do
              (__ArmCertEndOfDecode ())
              sailThrow ((Error_Undefined ())))
          | .Constraint_NOP =>
            (do
              (__ArmCertEndOfDecode ())
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-inputs/15-instrs64.sail:28285.107-28285.108"
        match c with
        | .Constraint_NONE => (pure (false))
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
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) offset postindex
    (Sail.Int.toNatChecked (regsize)) rt_unknown is_signed (Sail.Int.toNatChecked (t)) tagchecked
    wb_unknown wback)


def decode_ldapur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int :=
    (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) +++ size))
  if ((scale >b 4) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let offset : (BitVec 64) := (sign_extend imm9 64)
      let n : Int := (BitVec.toNat Rn)
      let t : Int := (BitVec.toNat Rt)
      let nontemporal : Bool := false
      let memop : MemOp :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
      let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
      ArmFull.assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "sail-inputs/15-instrs64.sail:28378.72-28378.73"
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered
        (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) offset postindex
        (Sail.Int.toNatChecked (t)) tagchecked wback))


def decode_stlur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int :=
    (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) +++ size))
  if ((scale >b 4) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let offset : (BitVec 64) := (sign_extend imm9 64)
      let n : Int := (BitVec.toNat Rn)
      let t : Int := (BitVec.toNat Rt)
      let nontemporal : Bool := false
      let memop : MemOp :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
      let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
      ArmFull.assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "sail-inputs/15-instrs64.sail:28408.72-28408.73"
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered
        (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) offset postindex
        (Sail.Int.toNatChecked (t)) tagchecked wback))


def decode_ldar_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset : Nat := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset regsize rt_unknown (Sail.Int.toNatChecked (t)) tagchecked
    wback)


def decode_ldarb_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset : Nat := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset regsize rt_unknown (Sail.Int.toNatChecked (t)) tagchecked
    wback)


def decode_ldarh_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset : Nat := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset regsize rt_unknown (Sail.Int.toNatChecked (t)) tagchecked
    wback)


def decode_ldlar_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset : Nat := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset regsize rt_unknown (Sail.Int.toNatChecked (t)) tagchecked
    wback)


def decode_ldlarb_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset : Nat := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset regsize rt_unknown (Sail.Int.toNatChecked (t)) tagchecked
    wback)


def decode_ldlarh_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset : Nat := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset regsize rt_unknown (Sail.Int.toNatChecked (t)) tagchecked
    wback)


def decode_stllr_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset : Nat := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset regsize rt_unknown (Sail.Int.toNatChecked (t)) tagchecked
    wback)


def decode_stllrb_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset : Nat := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset regsize rt_unknown (Sail.Int.toNatChecked (t)) tagchecked
    wback)


def decode_stllrh_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset : Nat := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset regsize rt_unknown (Sail.Int.toNatChecked (t)) tagchecked
    wback)


def decode_stlr_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset : Nat := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset regsize rt_unknown (Sail.Int.toNatChecked (t)) tagchecked
    wback)


def decode_stlr_aarch64_instrs_memory_ordered_writeback (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let memop : MemOp := MemOp_STORE
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let limitedordered : Bool := false
  let regsize : Int :=
    if ((size == 0b11#2) : Bool)
    then 64
    else 32
  let datasize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let offset : Int := ((Neg.neg 1) *i (Int.shiftl 1 (BitVec.toNat size)))
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((wback && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-inputs/15-instrs64.sail:28844.107-28844.108"
        match c with
        | .Constraint_NONE => (pure (false))
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
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (regsize)) rt_unknown
    (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_stlrb_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset : Nat := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset regsize rt_unknown (Sail.Int.toNatChecked (t)) tagchecked
    wback)


def decode_stlrh_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let s : Int := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset : Nat := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let regsize : Nat :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize : Int := elsize
  let tagchecked : Bool := (n != 31)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered (Sail.Int.toNatChecked (datasize)) limitedordered memop
    (Sail.Int.toNatChecked (n)) offset regsize rt_unknown (Sail.Int.toNatChecked (t)) tagchecked
    wback)


def decode_ldaxp_aarch64_instrs_memory_exclusive_pair (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) : SailM Unit := do
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
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29042.84-29042.85"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29059.88-29059.89"
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
                    c Constraint_NOP))) "sail-inputs/15-instrs64.sail:29075.88-29075.89"
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


end ArmFull.Functions
