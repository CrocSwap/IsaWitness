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
import ArmFull.Fn.M0144
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

def decode_str_reg_gen_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
  let memop ← (( do (undefined_MemOp (← occLabel 4569) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4570) ()) ) : SailM Bool )
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
  let c ← (( do (undefined_Constraint (← occLabel 4571) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36006.113-36006.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36025.107-36025.108"
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


def decode_strb_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
  let memop ← (( do (undefined_MemOp (← occLabel 4572) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4573) ()) ) : SailM Bool )
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
  let c ← (( do (undefined_Constraint (← occLabel 4574) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36103.113-36103.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36122.107-36122.108"
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


def decode_strh_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
  let memop ← (( do (undefined_MemOp (← occLabel 4575) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4576) ()) ) : SailM Bool )
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
  let c ← (( do (undefined_Constraint (← occLabel 4577) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36200.113-36200.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36219.107-36219.108"
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


def decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int :=
    (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) +++ size))
  if ((scale >b 4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
  let memop : MemOp :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  ArmFull.assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36320.72-36320.73"
  (execute_aarch64_instrs_memory_single_simdfp_register (Sail.Int.toNatChecked (datasize))
    extend_type (Sail.Int.toNatChecked (m)) memop (Sail.Int.toNatChecked (n)) nontemporal postindex
    (Sail.Int.toNatChecked (shift)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int :=
    (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) +++ size))
  if ((scale >b 4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
  let memop : MemOp :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  ArmFull.assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36357.72-36357.73"
  (execute_aarch64_instrs_memory_single_simdfp_register (Sail.Int.toNatChecked (datasize))
    extend_type (Sail.Int.toNatChecked (m)) memop (Sail.Int.toNatChecked (n)) nontemporal postindex
    (Sail.Int.toNatChecked (shift)) (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ldra_aarch64_instrs_memory_single_general_immediate_signed_pac (Rt : (BitVec 5)) (Rn : (BitVec 5)) (W : (BitVec 1)) (imm9 : (BitVec 9)) (S : (BitVec 1)) (M : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
          (pure (((! w__0) : Bool)))) || ((size != 0b11#2) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let n : Int := (BitVec.toNat Rn)
  let wback : Bool := (W == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let S10 : (BitVec 10) := (S +++ imm9)
  let scale : Nat := 3
  let offset : (BitVec 64) := ((sign_extend S10 64) <<< scale)
  let nontemporal : Bool := false
  let memop : MemOp := MemOp_LOAD
  let tagchecked : Bool := (wback || (n != 31))
  (execute_aarch64_instrs_memory_single_general_immediate_signed_pac memop
    (Sail.Int.toNatChecked (n)) nontemporal offset (Sail.Int.toNatChecked (t)) tagchecked use_key_a
    wback)


def decode_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp (← occLabel 4585) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4586) ()) ) : SailM Bool )
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
  let c ← (( do (undefined_Constraint (← occLabel 4587) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36647.113-36647.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36666.107-36666.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) nontemporal offset
    postindex (Sail.Int.toNatChecked (regsize)) rt_unknown is_signed (Sail.Int.toNatChecked (t))
    tagchecked wb_unknown wback)


def decode_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp (← occLabel 4588) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4589) ()) ) : SailM Bool )
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
  let c ← (( do (undefined_Constraint (← occLabel 4590) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36733.113-36733.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36752.107-36752.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) nontemporal offset
    postindex (Sail.Int.toNatChecked (regsize)) rt_unknown is_signed (Sail.Int.toNatChecked (t))
    tagchecked wb_unknown wback)


def decode_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp (← occLabel 4591) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4592) ()) ) : SailM Bool )
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
  let c ← (( do (undefined_Constraint (← occLabel 4593) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36819.113-36819.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36838.107-36838.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) nontemporal offset
    postindex (Sail.Int.toNatChecked (regsize)) rt_unknown is_signed (Sail.Int.toNatChecked (t))
    tagchecked wb_unknown wback)


end ArmFull.Functions
