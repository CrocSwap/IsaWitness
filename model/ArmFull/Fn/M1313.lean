import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0018
import ArmFull.Fn.M0019
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0198
import ArmFull.Fn.M1187
import ArmFull.Fn.M1188

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

def decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp (← occLabel 4640) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4641) ()) ) : SailM Bool )
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
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint (← occLabel 4642) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:38319.113-38319.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:38338.107-38338.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) nontemporal offset
    postindex (Sail.Int.toNatChecked (regsize)) rt_unknown is_signed (Sail.Int.toNatChecked (t))
    tagchecked wb_unknown wback)


def decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp (← occLabel 4643) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4644) ()) ) : SailM Bool )
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
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint (← occLabel 4645) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:38409.113-38409.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:38428.107-38428.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) nontemporal offset
    postindex (Sail.Int.toNatChecked (regsize)) rt_unknown is_signed (Sail.Int.toNatChecked (t))
    tagchecked wb_unknown wback)


def decode_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int := (BitVec.toNat size)
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend imm12 64) <<< scale)
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp (← occLabel 4680) ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool_at (← occLabel 4681) ()) ) : SailM Bool )
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
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint (← occLabel 4682) ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let w__0 ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        let c := (w__0 : Constraint)
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:39889.113-39889.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:39908.107-39908.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_unsigned
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) nontemporal offset
    postindex (Sail.Int.toNatChecked (regsize)) rt_unknown is_signed (Sail.Int.toNatChecked (t))
    tagchecked wb_unknown wback)


def decode_setp_aarch64_instrs_memory_mcpymset_set (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage (← occLabel 4769) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:43117.58-43117.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_set (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_setpn_aarch64_instrs_memory_mcpymset_set (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage (← occLabel 4770) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:43173.58-43173.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_set (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_setpt_aarch64_instrs_memory_mcpymset_set (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage (← occLabel 4771) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:43229.58-43229.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_set (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_setptn_aarch64_instrs_memory_mcpymset_set (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage (← occLabel 4772) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:43285.58-43285.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_set (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_setgp_aarch64_instrs_memory_mcpymset_setg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage (← occLabel 4778) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:43530.58-43530.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_setg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_setgpn_aarch64_instrs_memory_mcpymset_setg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage (← occLabel 4779) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:43589.58-43589.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_setg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_setgpt_aarch64_instrs_memory_mcpymset_setg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage (← occLabel 4780) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:43648.58-43648.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_setg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_setgptn_aarch64_instrs_memory_mcpymset_setg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage (← occLabel 4781) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:43707.58-43707.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_setg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_st2g_aarch64_instrs_integer_tags_mcsettagpairpost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Xn)
  let t : Int := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := true
  let zero_data : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettagpairpost (Sail.Int.toNatChecked (n)) offset postindex
    (Sail.Int.toNatChecked (t)) writeback zero_data)


end ArmFull.Functions
