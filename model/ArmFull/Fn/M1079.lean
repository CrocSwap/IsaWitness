import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0087
import ArmFull.Fn.M0118
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0198
import ArmFull.Fn.M0216
import ArmFull.Fn.M0237
import ArmFull.Fn.M0257
import ArmFull.Fn.M1043

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

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, t : Nat, t2 : Nat, k_tagchecked :
  Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_ld_128_ldclrp (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4437) 64) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescAtomicOp op acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let w__2 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let store_value : (BitVec 128) :=
    if (w__2 : Bool)
    then (value1_name +++ value2_name)
    else (value2_name +++ value1_name)
  let comparevalue ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let data ← (( do (MemAtomic address comparevalue store_value accdesc) ) : SailM (BitVec 128) )
  let w__3 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb data 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb data 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb data 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb data 127 64)))


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, t : Nat, t2 : Nat, k_tagchecked :
  Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_ld_128_ldsetp (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4581) 64) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescAtomicOp op acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let w__2 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let store_value : (BitVec 128) :=
    if (w__2 : Bool)
    then (value1_name +++ value2_name)
    else (value2_name +++ value1_name)
  let comparevalue ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let data ← (( do (MemAtomic address comparevalue store_value accdesc) ) : SailM (BitVec 128) )
  let w__3 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb data 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb data 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb data 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb data 127 64)))


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked
  : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_cas (acquire : Bool) (n : Nat) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4687) 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let compdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4688) 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4689) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_CAS soft acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let w__4 ← (( do (MemAtomicRCW address compdata newdata accdesc) ) : SailM
    ((BitVec 4) × (BitVec 64)) )
  let (tup__0, tup__1) := (w__4 : ((BitVec 4) × (BitVec 64)))
  let nzcv : (BitVec 4) := tup__0
  let readdata : (BitVec 64) := tup__1
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set s 64 readdata)


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked
  : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_cas_128 (acquire : Bool) (n : Nat) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4690) 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4691) 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4692) 4) ) : SailM (BitVec 4) )
  let s1 ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let s2 ← (( do (X_read (s +i 1) 64) ) : SailM (BitVec 64) )
  let t1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let t2 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_CAS soft acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let w__2 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let compdata : (BitVec 128) :=
    if (w__2 : Bool)
    then (s1 +++ s2)
    else (s2 +++ s1)
  let w__3 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let newdata : (BitVec 128) :=
    if (w__3 : Bool)
    then (t1 +++ t2)
    else (t2 +++ t1)
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let w__6 ← (( do (MemAtomicRCW address compdata newdata accdesc) ) : SailM
    ((BitVec 4) × (BitVec 128)) )
  let (tup__0, tup__1) := (w__6 : ((BitVec 4) × (BitVec 128)))
  let nzcv : (BitVec 4) := tup__0
  let readdata : (BitVec 128) := tup__1
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__10 with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  let w__11 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  if (w__11 : Bool)
  then
    (do
      (X_set s 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set (s +i 1) 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set s 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set (s +i 1) 64 (Sail.BitVec.extractLsb readdata 127 64)))


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked
  : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_ld_rcwclr (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4693) 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4694) 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4695) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let compdata ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let w__4 ← (( do (MemAtomicRCW address compdata newdata accdesc) ) : SailM
    ((BitVec 4) × (BitVec 64)) )
  let (tup__0, tup__1) := (w__4 : ((BitVec 4) × (BitVec 64)))
  let nzcv : (BitVec 4) := tup__0
  let readdata : (BitVec 64) := tup__1
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set t 64 readdata)


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, k_soft : Bool, t : Nat, t2 : Nat, k_tagchecked
  : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_ld_128_rcwclrp (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (soft : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4696) 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4697) 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4698) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let w__4 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let newdata : (BitVec 128) :=
    if (w__4 : Bool)
    then (value1_name +++ value2_name)
    else (value2_name +++ value1_name)
  let compdata ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let w__5 ← (( do (MemAtomicRCW address compdata newdata accdesc) ) : SailM
    ((BitVec 4) × (BitVec 128)) )
  let (tup__0, tup__1) := (w__5 : ((BitVec 4) × (BitVec 128)))
  let nzcv : (BitVec 4) := tup__0
  let readdata : (BitVec 128) := tup__1
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  let w__10 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  if (w__10 : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 127 64)))


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked
  : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_cas (acquire : Bool) (n : Nat) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4699) 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let compdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4700) 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4701) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_CAS soft acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let w__4 ← (( do (MemAtomicRCW address compdata newdata accdesc) ) : SailM
    ((BitVec 4) × (BitVec 64)) )
  let (tup__0, tup__1) := (w__4 : ((BitVec 4) × (BitVec 64)))
  let nzcv : (BitVec 4) := tup__0
  let readdata : (BitVec 64) := tup__1
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set s 64 readdata)


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked
  : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_cas_128 (acquire : Bool) (n : Nat) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4702) 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4703) 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4704) 4) ) : SailM (BitVec 4) )
  let s1 ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let s2 ← (( do (X_read (s +i 1) 64) ) : SailM (BitVec 64) )
  let t1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let t2 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_CAS soft acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let w__2 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let compdata : (BitVec 128) :=
    if (w__2 : Bool)
    then (s1 +++ s2)
    else (s2 +++ s1)
  let w__3 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let newdata : (BitVec 128) :=
    if (w__3 : Bool)
    then (t1 +++ t2)
    else (t2 +++ t1)
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let w__6 ← (( do (MemAtomicRCW address compdata newdata accdesc) ) : SailM
    ((BitVec 4) × (BitVec 128)) )
  let (tup__0, tup__1) := (w__6 : ((BitVec 4) × (BitVec 128)))
  let nzcv : (BitVec 4) := tup__0
  let readdata : (BitVec 128) := tup__1
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__10 with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  let w__11 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  if (w__11 : Bool)
  then
    (do
      (X_set s 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set (s +i 1) 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set s 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set (s +i 1) 64 (Sail.BitVec.extractLsb readdata 127 64)))


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked
  : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_ld_rcwsclr (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4705) 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4706) 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4707) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let compdata ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let w__4 ← (( do (MemAtomicRCW address compdata newdata accdesc) ) : SailM
    ((BitVec 4) × (BitVec 64)) )
  let (tup__0, tup__1) := (w__4 : ((BitVec 4) × (BitVec 64)))
  let nzcv : (BitVec 4) := tup__0
  let readdata : (BitVec 64) := tup__1
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set t 64 readdata)


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, k_soft : Bool, t : Nat, t2 : Nat, k_tagchecked
  : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_ld_128_rcwsclrp (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (soft : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4708) 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4709) 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4710) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let w__4 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let newdata : (BitVec 128) :=
    if (w__4 : Bool)
    then (value1_name +++ value2_name)
    else (value2_name +++ value1_name)
  let compdata ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let w__5 ← (( do (MemAtomicRCW address compdata newdata accdesc) ) : SailM
    ((BitVec 4) × (BitVec 128)) )
  let (tup__0, tup__1) := (w__5 : ((BitVec 4) × (BitVec 128)))
  let nzcv : (BitVec 4) := tup__0
  let readdata : (BitVec 128) := tup__1
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  let w__10 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  if (w__10 : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 127 64)))


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked
  : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_ld_rcwset (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4711) 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4712) 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4713) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let compdata ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let w__4 ← (( do (MemAtomicRCW address compdata newdata accdesc) ) : SailM
    ((BitVec 4) × (BitVec 64)) )
  let (tup__0, tup__1) := (w__4 : ((BitVec 4) × (BitVec 64)))
  let nzcv : (BitVec 4) := tup__0
  let readdata : (BitVec 64) := tup__1
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set t 64 readdata)


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, k_soft : Bool, t : Nat, t2 : Nat, k_tagchecked
  : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_ld_128_rcwsetp (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (soft : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4714) 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4715) 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4716) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let w__4 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let newdata : (BitVec 128) :=
    if (w__4 : Bool)
    then (value1_name +++ value2_name)
    else (value2_name +++ value1_name)
  let compdata ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let w__5 ← (( do (MemAtomicRCW address compdata newdata accdesc) ) : SailM
    ((BitVec 4) × (BitVec 128)) )
  let (tup__0, tup__1) := (w__5 : ((BitVec 4) × (BitVec 128)))
  let nzcv : (BitVec 4) := tup__0
  let readdata : (BitVec 128) := tup__1
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  let w__10 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  if (w__10 : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 127 64)))


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked
  : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_ld_rcwsset (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4717) 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4718) 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4719) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let compdata ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let w__4 ← (( do (MemAtomicRCW address compdata newdata accdesc) ) : SailM
    ((BitVec 4) × (BitVec 64)) )
  let (tup__0, tup__1) := (w__4 : ((BitVec 4) × (BitVec 64)))
  let nzcv : (BitVec 4) := tup__0
  let readdata : (BitVec 64) := tup__1
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set t 64 readdata)


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, k_soft : Bool, t : Nat, t2 : Nat, k_tagchecked
  : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_ld_128_rcwssetp (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (soft : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4720) 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4721) 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4722) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let w__4 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let newdata : (BitVec 128) :=
    if (w__4 : Bool)
    then (value1_name +++ value2_name)
    else (value2_name +++ value1_name)
  let compdata ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let w__5 ← (( do (MemAtomicRCW address compdata newdata accdesc) ) : SailM
    ((BitVec 4) × (BitVec 128)) )
  let (tup__0, tup__1) := (w__5 : ((BitVec 4) × (BitVec 128)))
  let nzcv : (BitVec 4) := tup__0
  let readdata : (BitVec 128) := tup__1
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  let w__10 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  if (w__10 : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 127 64)))


end ArmFull.Functions
