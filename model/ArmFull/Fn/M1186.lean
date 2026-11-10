import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0040
import ArmFull.Fn.M0049
import ArmFull.Fn.M0061
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0112
import ArmFull.Fn.M0117
import ArmFull.Fn.M0118
import ArmFull.Fn.M0123
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0158
import ArmFull.Fn.M0185
import ArmFull.Fn.M0215
import ArmFull.Fn.M0237
import ArmFull.Fn.M0257
import ArmFull.Fn.M0581
import ArmFull.Fn.M0840
import ArmFull.Fn.M1142

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

/-- Type quantifiers: datasize : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, t : Nat, k_tagchecked
  : Bool, k_wback : Bool, 0 ≤ t ∧
  t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64, 128, 256, 512, 1024] -/
def execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let address ← (( do (undefined_bitvector_at (← occLabel 4460) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4461)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor
    )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32419.62-32419.63"
      let data ← (( do ((Sail.BitVec.castWidth ) <$> (V_read t datasize)) ) : SailM
        (BitVec datasize) )
      (Mem_set address (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc
        (Sail.BitVec.castWidth data)))
  | .MemOp_LOAD =>
    (do
      let data ← (( do
        ((Sail.BitVec.castWidth ) <$> ((Mem_read address
          (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc))) ) : SailM (BitVec datasize) )
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32425.62-32425.63"
      (V_set t datasize (Sail.BitVec.castWidth data)))
  | _ => (pure (()))
  if (wback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then
        (do
          (SP_set address))
      else
        (do
          (X_set n 64 address)))
  else (pure (()))
  let w__2 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (SPESampleSIMDFPLoadStore ()))
  else (pure (()))


/-- Type quantifiers: k_is_signed : Bool, k_nontemporal : Bool, size : Nat, t : Nat, k_tagchecked :
  Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem size [4, 8] -/
def execute_aarch64_instrs_memory_literal_general (memop : MemOp) (nontemporal : Bool) (offset : (BitVec 64)) (is_signed : Bool) (size : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
  let address : (BitVec 64) := (w__0 + offset)
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4462)
      (Sail.Int.toNatChecked ((size *i 8))))) ) : SailM (BitVec (size * 8)) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__1.EL != EL0)
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  match memop with
  | .MemOp_LOAD =>
    (do
      let data ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read address size accdesc)) ) : SailM
        (BitVec (size * 8)) )
      if (is_signed : Bool)
      then
        (do
          (X_set t 64 (sign_extend data 64)))
      else
        (do
          (X_set t (Sail.Int.toNatChecked ((size *i 8))) (Sail.BitVec.castWidth data))))
  | .MemOp_PREFETCH =>
    (do
      (Prefetch address (integer_subrange t 4 0)))
  | _ => (pure (()))
  let w__2 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: k_nontemporal : Bool, size : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧
  t ≤ 31 ∧ List.elem size [4, 8, 16] -/
def execute_aarch64_instrs_memory_literal_simdfp (nontemporal : Bool) (offset : (BitVec 64)) (size : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
  let address : (BitVec 64) := (w__0 + offset)
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__1.EL != EL0)
  (CheckFPEnabled64 ())
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM
    AccessDescriptor )
  let data ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read address size accdesc)) ) : SailM
    (BitVec (size * 8)) )
  (V_set t (Sail.Int.toNatChecked ((size *i 8))) (Sail.BitVec.castWidth data))
  let w__2 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (SPESampleSIMDFPLoadStore ()))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, n : Nat, k_nontemporal : Bool, k_postindex
  : Bool, regsize : Nat, k_rt_unknown : Bool, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback
  : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4463) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4464)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__0.EL != EL0)
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((bne memop MemOp_PREFETCH) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data ← (( do
        if (rt_unknown : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)))
        else
          (do
            ((Sail.BitVec.castWidth ) <$> (X_read t datasize))) ) : SailM (BitVec datasize) )
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) false t (regsize == 64) false)
        else ()
      (Mem_set address (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc
        (Sail.BitVec.castWidth data)))
  | .MemOp_LOAD =>
    (do
      let _ : Unit :=
        if ((! wback) : Bool)
        then
          (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) is_signed t (regsize == 64) false)
        else ()
      let data ← (( do
        ((Sail.BitVec.castWidth ) <$> ((Mem_read address
          (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc))) ) : SailM (BitVec datasize) )
      if (is_signed : Bool)
      then
        (do
          ArmFull.assert ((datasize >b 0) && (regsize ≥b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32855.72-32855.73"
          (X_set t regsize (Sail.BitVec.castWidth (sign_extend data regsize))))
      else
        (do
          ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:32858.73-32858.74"
          (X_set t regsize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend data regsize)))))
  | .MemOp_PREFETCH =>
    (do
      (Prefetch address (integer_subrange t 4 0)))
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then
          (do
            (__UNKNOWN_bits 64))
        else
          (let address : (BitVec 64) :=
            if (postindex : Bool)
            then (address + offset)
            else address
          (pure (address))) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then
        (do
          (SP_set address))
      else
        (do
          (X_set n 64 address)))
  else (pure (()))
  let w__6 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, m : Nat, n : Nat, k_nontemporal : Bool, k_postindex
  : Bool, regsize : Nat, k_rt_unknown : Bool, shift : Nat, t : Nat, k_tagchecked : Bool, k_wb_unknown
  : Bool, k_wback : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem shift [0, 1, 2, 3] ∧
  List.elem regsize [32, 64] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_register (datasize : Nat) (extend_type : ExtendType) (m : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (shift : Nat) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let offset ← (( do (ExtendReg m extend_type shift 64) ) : SailM (BitVec 64) )
  let address ← (( do (undefined_bitvector_at (← occLabel 4546) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4547)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__0.EL != EL0)
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((bne memop MemOp_PREFETCH) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data ← (( do
        if (rt_unknown : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)))
        else
          (do
            ((Sail.BitVec.castWidth ) <$> (X_read t datasize))) ) : SailM (BitVec datasize) )
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) false t (regsize == 64) false)
        else ()
      (Mem_set address (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc
        (Sail.BitVec.castWidth data)))
  | .MemOp_LOAD =>
    (do
      let _ : Unit :=
        if ((! wback) : Bool)
        then
          (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) is_signed t (regsize == 64) false)
        else ()
      let data ← (( do
        ((Sail.BitVec.castWidth ) <$> ((Mem_read address
          (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc))) ) : SailM (BitVec datasize) )
      if (is_signed : Bool)
      then
        (do
          ArmFull.assert ((datasize >b 0) && (regsize ≥b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35245.72-35245.73"
          (X_set t regsize (Sail.BitVec.castWidth (sign_extend data regsize))))
      else
        (do
          ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:35248.73-35248.74"
          (X_set t regsize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend data regsize)))))
  | .MemOp_PREFETCH =>
    (do
      (Prefetch address (integer_subrange t 4 0)))
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then
          (do
            (__UNKNOWN_bits 64))
        else
          (let address : (BitVec 64) :=
            if (postindex : Bool)
            then (address + offset)
            else address
          (pure (address))) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then
        (do
          (SP_set address))
      else
        (do
          (X_set n 64 address)))
  else (pure (()))
  let w__6 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, m : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, shift
  : Nat, t : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem shift [0, 1, 2, 3, 4, 5, 6, 7] ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [8, 16, 32, 64, 128, 256, 512, 1024] -/
def execute_aarch64_instrs_memory_single_simdfp_register (datasize : Nat) (extend_type : ExtendType) (m : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (postindex : Bool) (shift : Nat) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  let offset ← (( do (ExtendReg m extend_type shift 64) ) : SailM (BitVec 64) )
  (CheckFPEnabled64 ())
  let address ← (( do (undefined_bitvector_at (← occLabel 4578) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4579)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor
    )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36272.62-36272.63"
      let data ← (( do ((Sail.BitVec.castWidth ) <$> (V_read t datasize)) ) : SailM
        (BitVec datasize) )
      (Mem_set address (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc
        (Sail.BitVec.castWidth data)))
  | .MemOp_LOAD =>
    (do
      let data ← (( do
        ((Sail.BitVec.castWidth ) <$> ((Mem_read address
          (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc))) ) : SailM (BitVec datasize) )
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36278.62-36278.63"
      (V_set t datasize (Sail.BitVec.castWidth data)))
  | _ => (pure (()))
  if (wback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then
        (do
          (SP_set address))
      else
        (do
          (X_set n 64 address)))
  else (pure (()))
  let w__2 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (SPESampleSIMDFPLoadStore ()))
  else (pure (()))


/-- Type quantifiers: n : Nat, k_nontemporal : Bool, t : Nat, k_tagchecked : Bool, k_use_key_a :
  Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_single_general_immediate_signed_pac (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (t : Nat) (tagchecked : Bool) (use_key_a : Bool) (wback__arg : Bool) : SailM Unit := do
  let wback : Bool := wback__arg
  let address ← (( do (undefined_bitvector_at (← occLabel 4580) 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__0.EL != EL0)
  let wb_unknown : Bool := false
  let auth_then_branch : Bool := true
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  let (wb_unknown, wback) ← (( do
    if (((wback && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36386.113-36386.114"
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
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let _ : Unit :=
    if ((! wback) : Bool)
    then (AArch64_SetLSInstructionSyndrome 8 false t true false)
    else ()
  let address ← (( do
    if (use_key_a : Bool)
    then
      (do
        let w__3 ← (( do (X_read 31 64) ) : SailM (BitVec 64) )
        (AuthDA address w__3 auth_then_branch))
    else
      (do
        let w__5 ← (( do (X_read 31 64) ) : SailM (BitVec 64) )
        (AuthDB address w__5 auth_then_branch)) ) : SailM (BitVec 64) )
  if ((n == 31) : Bool)
  then
    (do
      (CheckSPAlignment ()))
  else (pure (()))
  let address : (BitVec 64) := (address + offset)
  let data ← (( do (Mem_read address 8 accdesc) ) : SailM (BitVec 64) )
  (X_set t 64 data)
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then
          (do
            (__UNKNOWN_bits 64))
        else (pure (address)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then
        (do
          (SP_set address))
      else
        (do
          (X_set n 64 address)))
  else (pure (()))
  let w__8 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__8 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, n : Nat, k_nontemporal : Bool, k_postindex
  : Bool, regsize : Nat, k_rt_unknown : Bool, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback
  : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4583) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4584)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let privileged ← (( do (AArch64_IsUnprivAccessPriv ()) ) : SailM Bool )
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((bne memop MemOp_PREFETCH) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data ← (( do
        if (rt_unknown : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)))
        else
          (do
            ((Sail.BitVec.castWidth ) <$> (X_read t datasize))) ) : SailM (BitVec datasize) )
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) false t (regsize == 64) false)
        else ()
      (Mem_set address (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc
        (Sail.BitVec.castWidth data)))
  | .MemOp_LOAD =>
    (do
      let _ : Unit :=
        if ((! wback) : Bool)
        then
          (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) is_signed t (regsize == 64) false)
        else ()
      let data ← (( do
        ((Sail.BitVec.castWidth ) <$> ((Mem_read address
          (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc))) ) : SailM (BitVec datasize) )
      if (is_signed : Bool)
      then
        (do
          ArmFull.assert ((datasize >b 0) && (regsize ≥b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36581.72-36581.73"
          (X_set t regsize (Sail.BitVec.castWidth (sign_extend data regsize))))
      else
        (do
          ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:36584.73-36584.74"
          (X_set t regsize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend data regsize)))))
  | .MemOp_PREFETCH =>
    (do
      (Prefetch address (integer_subrange t 4 0)))
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then
          (do
            (__UNKNOWN_bits 64))
        else
          (let address : (BitVec 64) :=
            if (postindex : Bool)
            then (address + offset)
            else address
          (pure (address))) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then
        (do
          (SP_set address))
      else
        (do
          (X_set n 64 address)))
  else (pure (()))
  let w__5 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: datasize : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, t : Nat, k_tagchecked
  : Bool, k_wback : Bool, 0 ≤ t ∧
  t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64, 128, 256, 512, 1024] -/
def execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let address ← (( do (undefined_bitvector_at (← occLabel 4612) 64) ) : SailM (BitVec 64) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4613)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor
    )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:37404.62-37404.63"
      let data ← (( do ((Sail.BitVec.castWidth ) <$> (V_read t datasize)) ) : SailM
        (BitVec datasize) )
      (Mem_set address (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc
        (Sail.BitVec.castWidth data)))
  | .MemOp_LOAD =>
    (do
      let data ← (( do
        ((Sail.BitVec.castWidth ) <$> ((Mem_read address
          (Sail.Int.toNatChecked ((Int.ediv datasize 8))) accdesc))) ) : SailM (BitVec datasize) )
      ArmFull.assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:37410.62-37410.63"
      (V_set t datasize (Sail.BitVec.castWidth data)))
  | _ => (pure (()))
  if (wback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then
        (do
          (SP_set address))
      else
        (do
          (X_set n 64 address)))
  else (pure (()))
  let w__2 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (SPESampleSIMDFPLoadStore ()))
  else (pure (()))


end ArmFull.Functions
