import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0117
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

def decode_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31125.84-31125.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31139.54-31139.55"
  (execute_aarch64_instrs_memory_pair_simdfp_no_alloc (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wback)


def decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31231.84-31231.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31245.54-31245.55"
  (execute_aarch64_instrs_memory_pair_simdfp_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wback)


def decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31280.84-31280.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31294.54-31294.55"
  (execute_aarch64_instrs_memory_pair_simdfp_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wback)


def decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31329.84-31329.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31343.54-31343.55"
  (execute_aarch64_instrs_memory_pair_simdfp_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wback)


def decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31378.84-31378.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31392.54-31392.55"
  (execute_aarch64_instrs_memory_pair_simdfp_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wback)


def decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31427.84-31427.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31441.54-31441.55"
  (execute_aarch64_instrs_memory_pair_simdfp_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wback)


def decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31476.84-31476.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31490.54-31490.55"
  (execute_aarch64_instrs_memory_pair_simdfp_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wback)


def decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31620.113-31620.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31639.107-31639.108"
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31658.84-31658.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31672.44-31672.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown is_signed
    (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked wb_unknown wback)


def decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31709.113-31709.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31728.107-31728.108"
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31747.84-31747.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31761.44-31761.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown is_signed
    (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked wb_unknown wback)


def decode_ldp_gen_aarch64_instrs_memory_pair_general_offset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31798.113-31798.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31817.107-31817.108"
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31836.84-31836.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31850.44-31850.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown is_signed
    (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked wb_unknown wback)


def decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31887.113-31887.114"
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
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31906.107-31906.108"
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
              c Constraint_NOP))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31925.84-31925.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:31939.44-31939.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) nontemporal offset postindex rt_unknown is_signed
    (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) tagchecked wb_unknown wback)


end ArmFull.Functions
