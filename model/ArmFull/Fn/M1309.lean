import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0018
import ArmFull.Fn.M0117
import ArmFull.Fn.M0123
import ArmFull.Fn.M1186

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

def decode_ldrb_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access option_name 1)])) == 0#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let m : Int := (BitVec.toNat Rm)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp (← occLabel 4551) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4552) ()) ) : SailM Bool )
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
            let memop : MemOp := MemOp_PREFETCH
            if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            (pure ((is_signed, memop, regsize))))
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint (← occLabel 4553) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35417.113-35417.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35436.107-35436.108"
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
  (execute_aarch64_instrs_memory_single_general_register (Sail.Int.toNatChecked (datasize))
    extend_type (Sail.Int.toNatChecked (m)) memop (Sail.Int.toNatChecked (n)) nontemporal postindex
    (Sail.Int.toNatChecked (regsize)) rt_unknown (Sail.Int.toNatChecked (shift)) is_signed
    (Sail.Int.toNatChecked (t)) tagchecked wb_unknown wback)


def decode_ldrh_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access option_name 1)])) == 0#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let m : Int := (BitVec.toNat Rm)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp (← occLabel 4554) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4555) ()) ) : SailM Bool )
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
            let memop : MemOp := MemOp_PREFETCH
            if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            (pure ((is_signed, memop, regsize))))
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint (← occLabel 4556) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35514.113-35514.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35533.107-35533.108"
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
  (execute_aarch64_instrs_memory_single_general_register (Sail.Int.toNatChecked (datasize))
    extend_type (Sail.Int.toNatChecked (m)) memop (Sail.Int.toNatChecked (n)) nontemporal postindex
    (Sail.Int.toNatChecked (regsize)) rt_unknown (Sail.Int.toNatChecked (shift)) is_signed
    (Sail.Int.toNatChecked (t)) tagchecked wb_unknown wback)


def decode_ldrsb_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access option_name 1)])) == 0#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let m : Int := (BitVec.toNat Rm)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp (← occLabel 4557) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4558) ()) ) : SailM Bool )
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
            let memop : MemOp := MemOp_PREFETCH
            if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            (pure ((is_signed, memop, regsize))))
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint (← occLabel 4559) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35611.113-35611.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35630.107-35630.108"
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
  (execute_aarch64_instrs_memory_single_general_register (Sail.Int.toNatChecked (datasize))
    extend_type (Sail.Int.toNatChecked (m)) memop (Sail.Int.toNatChecked (n)) nontemporal postindex
    (Sail.Int.toNatChecked (regsize)) rt_unknown (Sail.Int.toNatChecked (shift)) is_signed
    (Sail.Int.toNatChecked (t)) tagchecked wb_unknown wback)


def decode_ldrsh_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access option_name 1)])) == 0#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let m : Int := (BitVec.toNat Rm)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp (← occLabel 4560) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4561) ()) ) : SailM Bool )
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
            let memop : MemOp := MemOp_PREFETCH
            if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            (pure ((is_signed, memop, regsize))))
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint (← occLabel 4562) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35708.113-35708.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35727.107-35727.108"
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
  (execute_aarch64_instrs_memory_single_general_register (Sail.Int.toNatChecked (datasize))
    extend_type (Sail.Int.toNatChecked (m)) memop (Sail.Int.toNatChecked (n)) nontemporal postindex
    (Sail.Int.toNatChecked (regsize)) rt_unknown (Sail.Int.toNatChecked (shift)) is_signed
    (Sail.Int.toNatChecked (t)) tagchecked wb_unknown wback)


def decode_ldrsw_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access option_name 1)])) == 0#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let m : Int := (BitVec.toNat Rm)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp (← occLabel 4563) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4564) ()) ) : SailM Bool )
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
            let memop : MemOp := MemOp_PREFETCH
            if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            (pure ((is_signed, memop, regsize))))
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint (← occLabel 4565) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35805.113-35805.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35824.107-35824.108"
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
  (execute_aarch64_instrs_memory_single_general_register (Sail.Int.toNatChecked (datasize))
    extend_type (Sail.Int.toNatChecked (m)) memop (Sail.Int.toNatChecked (n)) nontemporal postindex
    (Sail.Int.toNatChecked (regsize)) rt_unknown (Sail.Int.toNatChecked (shift)) is_signed
    (Sail.Int.toNatChecked (t)) tagchecked wb_unknown wback)


def decode_prfm_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let b__0 := Rt
  ArmFull.assert (! (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b11#2 : (BitVec 2))) : Bool)
    then true
    else false : Bool)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35862.14-35862.15"
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access option_name 1)])) == 0#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let m : Int := (BitVec.toNat Rm)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp (← occLabel 4566) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4567) ()) ) : SailM Bool )
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
            let memop : MemOp := MemOp_PREFETCH
            if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            (pure ((is_signed, memop, regsize))))
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint (← occLabel 4568) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35906.113-35906.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35925.107-35925.108"
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
  (execute_aarch64_instrs_memory_single_general_register (Sail.Int.toNatChecked (datasize))
    extend_type (Sail.Int.toNatChecked (m)) memop (Sail.Int.toNatChecked (n)) nontemporal postindex
    (Sail.Int.toNatChecked (regsize)) rt_unknown (Sail.Int.toNatChecked (shift)) is_signed
    (Sail.Int.toNatChecked (t)) tagchecked wb_unknown wback)


end ArmFull.Functions
