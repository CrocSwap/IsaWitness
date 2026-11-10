import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0117
import ArmFull.Fn.M1185
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

def decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)]))) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) != 0#1)
  let scale : Int :=
    (2 +i (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)]))))
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31976.113-31976.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31995.107-31995.108"
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32014.84-32014.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32028.44-32028.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown is_signed
    (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked wb_unknown wback)


def decode_ldpsw_aarch64_instrs_memory_pair_general_offset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)]))) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) != 0#1)
  let scale : Int :=
    (2 +i (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)]))))
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32065.113-32065.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32084.107-32084.108"
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32103.84-32103.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32117.44-32117.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown is_signed
    (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked wb_unknown wback)


def decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)]))) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) != 0#1)
  let scale : Int :=
    (2 +i (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)]))))
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32154.113-32154.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32173.107-32173.108"
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32192.84-32192.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32206.44-32206.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown is_signed
    (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked wb_unknown wback)


def decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)]))) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) != 0#1)
  let scale : Int :=
    (2 +i (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)]))))
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32243.113-32243.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32262.107-32262.108"
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32281.84-32281.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32295.44-32295.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown is_signed
    (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked wb_unknown wback)


def decode_stp_gen_aarch64_instrs_memory_pair_general_offset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)]))) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) != 0#1)
  let scale : Int :=
    (2 +i (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)]))))
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32332.113-32332.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32351.107-32351.108"
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32370.84-32370.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32384.44-32384.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown is_signed
    (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked wb_unknown wback)


def decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let scale : Int :=
    (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) +++ size))
  if ((scale >b 4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
  ArmFull.assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32462.72-32462.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) nontemporal offset
    postindex (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let scale : Int :=
    (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) +++ size))
  if ((scale >b 4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
  ArmFull.assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32492.72-32492.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) nontemporal offset
    postindex (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int :=
    (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) +++ size))
  if ((scale >b 4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend imm12 64) <<< scale)
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  ArmFull.assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32522.72-32522.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) nontemporal offset
    postindex (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let scale : Int :=
    (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) +++ size))
  if ((scale >b 4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
  ArmFull.assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32552.72-32552.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) nontemporal offset
    postindex (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let scale : Int :=
    (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) +++ size))
  if ((scale >b 4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
  ArmFull.assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32582.72-32582.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) nontemporal offset
    postindex (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale : Int :=
    (BitVec.toNat ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) +++ size))
  if ((scale >b 4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend imm12 64) <<< scale)
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  ArmFull.assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32612.72-32612.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx
    (Sail.Int.toNatChecked (datasize)) memop (Sail.Int.toNatChecked (n)) nontemporal offset
    postindex (Sail.Int.toNatChecked (t)) tagchecked wback)


def decode_ldr_lit_gen_aarch64_instrs_memory_literal_general (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_LOAD
  let is_signed : Bool := false
  let nontemporal : Bool := false
  let size : Int := 4
  let (is_signed, memop, size) : (Bool × MemOp × Int) :=
    match opc with
    | 0b00 =>
      (let size : Int := 4
      (is_signed, memop, size))
    | 0b01 =>
      (let size : Int := 8
      (is_signed, memop, size))
    | 0b10 =>
      (let size : Int := 4
      let is_signed : Bool := true
      (is_signed, memop, size))
    | _ =>
      (let memop : MemOp := MemOp_PREFETCH
      (is_signed, memop, size))
  let size : Int := size
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  let tagchecked : Bool := false
  (execute_aarch64_instrs_memory_literal_general memop nontemporal offset is_signed
    (Sail.Int.toNatChecked (size)) (Sail.Int.toNatChecked (t)) tagchecked)


def decode_ldrsw_lit_aarch64_instrs_memory_literal_general (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_LOAD
  let is_signed : Bool := false
  let nontemporal : Bool := false
  let size : Int := 4
  let (is_signed, memop, size) : (Bool × MemOp × Int) :=
    match opc with
    | 0b00 =>
      (let size : Int := 4
      (is_signed, memop, size))
    | 0b01 =>
      (let size : Int := 8
      (is_signed, memop, size))
    | 0b10 =>
      (let size : Int := 4
      let is_signed : Bool := true
      (is_signed, memop, size))
    | _ =>
      (let memop : MemOp := MemOp_PREFETCH
      (is_signed, memop, size))
  let size : Int := size
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  let tagchecked : Bool := false
  (execute_aarch64_instrs_memory_literal_general memop nontemporal offset is_signed
    (Sail.Int.toNatChecked (size)) (Sail.Int.toNatChecked (t)) tagchecked)


def decode_prfm_lit_aarch64_instrs_memory_literal_general (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_LOAD
  let is_signed : Bool := false
  let nontemporal : Bool := false
  let size : Int := 4
  let (is_signed, memop, size) : (Bool × MemOp × Int) :=
    match opc with
    | 0b00 =>
      (let size : Int := 4
      (is_signed, memop, size))
    | 0b01 =>
      (let size : Int := 8
      (is_signed, memop, size))
    | 0b10 =>
      (let size : Int := 4
      let is_signed : Bool := true
      (is_signed, memop, size))
    | _ =>
      (let memop : MemOp := MemOp_PREFETCH
      (is_signed, memop, size))
  let size : Int := size
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  let tagchecked : Bool := false
  (execute_aarch64_instrs_memory_literal_general memop nontemporal offset is_signed
    (Sail.Int.toNatChecked (size)) (Sail.Int.toNatChecked (t)) tagchecked)


end ArmFull.Functions
