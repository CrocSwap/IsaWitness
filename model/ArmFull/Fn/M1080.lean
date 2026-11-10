import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051
import ArmFull.Fn.M0061
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0118
import ArmFull.Fn.M0123
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0178
import ArmFull.Fn.M0198
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0216
import ArmFull.Fn.M0218
import ArmFull.Fn.M0237
import ArmFull.Fn.M0257
import ArmFull.Fn.M0259
import ArmFull.Fn.M0840
import ArmFull.Fn.M0852
import ArmFull.Fn.M1040
import ArmFull.Fn.M1043
import ArmFull.Fn.M1044

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

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked
  : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_swp (acquire : Bool) (n : Nat) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4723) 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4724) 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4725) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_SWP soft acquire release tagchecked) ) : SailM
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
def execute_aarch64_instrs_memory_rcws_swp_128 (acquire : Bool) (n : Nat) (release : Bool) (soft : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4726) 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4727) 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4728) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_SWP soft acquire release tagchecked) ) : SailM
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
def execute_aarch64_instrs_memory_rcw_swp (acquire : Bool) (n : Nat) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4729) 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4730) 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4731) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_SWP soft acquire release tagchecked) ) : SailM
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
def execute_aarch64_instrs_memory_rcw_swp_128 (acquire : Bool) (n : Nat) (release : Bool) (soft : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsD128Enabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let address ← (( do (undefined_bitvector_at (← occLabel 4732) 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector_at (← occLabel 4733) 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 4734) 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_SWP soft acquire release tagchecked) ) : SailM
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


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, fracbits : Int, k_is_unsigned
  : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_conv_int_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (fracbits : Int) (n : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4760)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do
    if (((elements == 1) : Bool) : Bool)
    then
      (do
        (IsMerging fpcr))
    else (pure false) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__2 : (BitVec esize))
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FixedToFP element fracbits is_unsigned fpcr rounding
              esize)) ) : SailM (BitVec esize) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__3))) )
            : SailM (BitVec 128) )
          let result := (w__4 : (BitVec 128))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n
  : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do
    if (((elements == 1) : Bool) : Bool)
    then
      (do
        (IsMerging fpcr))
    else (pure false) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4761)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__2 : (BitVec esize))
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FixedToFP element 0 is_unsigned fpcr rounding esize)) ) :
            SailM (BitVec esize) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__3))) )
            : SailM (BitVec 128) )
          let result := (w__4 : (BitVec 128))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: n : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧
  t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_st_acc_st64b (lst : (BitVec 2)) (memop : MemOp) (n : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  (CheckLDST64BEnabled ())
  let data ← (( do (undefined_bitvector_at (← occLabel 4985) 512) ) : SailM (BitVec 512) )
  let address ← (( do (undefined_bitvector_at (← occLabel 4986) 64) ) : SailM (BitVec 64) )
  let value_name ← (( do (undefined_bitvector_at (← occLabel 4987) 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescLS64 memop tagchecked) ) : SailM AccessDescriptor )
  let (data, value_name) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 7
    (do
      let mut loop_vars := (data, value_name)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (data, value_name) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (X_read (t +i i) 64) ) : SailM (BitVec 64) )
          let value_name := (w__0 : (BitVec 64))
          let w__1 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
          let value_name : (BitVec 64) :=
            if (w__1 : Bool)
            then (reverse_endianness value_name)
            else value_name
          let data : (BitVec 512) :=
            (Sail.BitVec.updateSubrange data (Sail.Int.toNatChecked ((63 +i (64 *i i))))
              (Sail.Int.toNatChecked ((64 *i i))) (Sail.BitVec.castWidth value_name))
          (pure ((data, value_name)))
      (pure loop_vars)) ) : SailM ((BitVec 512) × (BitVec 64)) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let _ : Unit := (SetLoadStoreType lst)
  let _ : Unit := (AArch64_SetLSInstructionSyndrome 64 false t true false)
  (MemStore64B address data accdesc)
  let w__4 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: n : Nat, s : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧
  t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_st_acc_st64bv (Rs : (BitVec 5)) (lst : (BitVec 2)) (memop : MemOp) (n : Nat) (s : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  (CheckST64BVEnabled ())
  let data ← (( do (undefined_bitvector_at (← occLabel 4988) 512) ) : SailM (BitVec 512) )
  let address ← (( do (undefined_bitvector_at (← occLabel 4989) 64) ) : SailM (BitVec 64) )
  let value_name ← (( do (undefined_bitvector_at (← occLabel 4990) 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescLS64 memop tagchecked) ) : SailM AccessDescriptor )
  let (data, value_name) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 7
    (do
      let mut loop_vars := (data, value_name)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (data, value_name) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (X_read (t +i i) 64) ) : SailM (BitVec 64) )
          let value_name := (w__0 : (BitVec 64))
          let w__1 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
          let value_name : (BitVec 64) :=
            if (w__1 : Bool)
            then (reverse_endianness value_name)
            else value_name
          let data : (BitVec 512) :=
            (Sail.BitVec.updateSubrange data (Sail.Int.toNatChecked ((63 +i (64 *i i))))
              (Sail.Int.toNatChecked ((64 *i i))) (Sail.BitVec.castWidth value_name))
          (pure ((data, value_name)))
      (pure loop_vars)) ) : SailM ((BitVec 512) × (BitVec 64)) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let _ : Unit := (SetLoadStoreType lst)
  let _ : Unit := (AArch64_SetLSInstructionSyndrome 64 false t true false)
  let _ : Unit := (SetIss2 Rs)
  let status ← (( do (MemStore64BWithRet address data accdesc) ) : SailM (BitVec 64) )
  if ((s != 31) : Bool)
  then
    (do
      (X_set s 64 status))
  else (pure (()))
  let w__4 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: n : Nat, s : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧
  t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_st_acc_st64bv0 (Rs : (BitVec 5)) (lst : (BitVec 2)) (memop : MemOp) (n : Nat) (s : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  (CheckST64BV0Enabled ())
  let data ← (( do (undefined_bitvector_at (← occLabel 4991) 512) ) : SailM (BitVec 512) )
  let address ← (( do (undefined_bitvector_at (← occLabel 4992) 64) ) : SailM (BitVec 64) )
  let value_name ← (( do (undefined_bitvector_at (← occLabel 4993) 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescLS64 memop tagchecked) ) : SailM AccessDescriptor )
  let Xt ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do readReg ACCDATA_EL1 ) : SailM (BitVec 64) )
  let value_name :=
    ((Sail.BitVec.updateSubrange value_name 31 0 (Sail.BitVec.extractLsb w__0 31 0)) : (BitVec 64))
  let value_name : (BitVec 64) :=
    (Sail.BitVec.updateSubrange value_name 63 32 (Sail.BitVec.extractLsb Xt 63 32))
  let w__1 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let value_name : (BitVec 64) :=
    if (w__1 : Bool)
    then (reverse_endianness value_name)
    else value_name
  let data : (BitVec 512) := (Sail.BitVec.updateSubrange data 63 0 value_name)
  let (data, value_name) ← (( do
    let loop_i_lower : Nat := 1
    let loop_i_upper : Nat := 7
    (do
      let mut loop_vars := (data, value_name)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (data, value_name) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (X_read (t +i i) 64) ) : SailM (BitVec 64) )
          let value_name := (w__2 : (BitVec 64))
          let w__3 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
          let value_name : (BitVec 64) :=
            if (w__3 : Bool)
            then (reverse_endianness value_name)
            else value_name
          let data : (BitVec 512) :=
            (Sail.BitVec.updateSubrange data (Sail.Int.toNatChecked ((63 +i (64 *i i))))
              (Sail.Int.toNatChecked ((64 *i i))) (Sail.BitVec.castWidth value_name))
          (pure ((data, value_name)))
      (pure loop_vars)) ) : SailM ((BitVec 512) × (BitVec 64)) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let _ : Unit := (SetLoadStoreType lst)
  let _ : Unit := (AArch64_SetLSInstructionSyndrome 64 false t true false)
  let _ : Unit := (SetIss2 Rs)
  let status ← (( do (MemStore64BWithRet address data accdesc) ) : SailM (BitVec 64) )
  if ((s != 31) : Bool)
  then
    (do
      (X_set s 64 status))
  else (pure (()))
  let w__6 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: k_acquire : Bool, datasize : Nat, n : Nat, regsize : Nat, k_release : Bool, s
  : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ s ∧
  s ≤ 31 ∧
  List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_atomicops_swp (acquire : Bool) (datasize : Nat) (n : Nat) (regsize : Nat) (release : Bool) (s : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 5017) 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescAtomicOp MemAtomicOp_SWP acquire release tagchecked) ) : SailM
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
  let store_value ← (( do ((Sail.BitVec.castWidth ) <$> (X_read s datasize)) ) : SailM
    (BitVec datasize) )
  let comparevalue ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
    (BitVec datasize) )
  let data ← (( do (MemAtomic address comparevalue store_value accdesc) ) : SailM
    (BitVec datasize) )
  ArmFull.assert (regsize ≥b datasize) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:51787.44-51787.45"
  (X_set t regsize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend data regsize)))
  let w__2 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let ar : (BitVec 1) :=
        if ((acquire || release) : Bool)
        then 1#1
        else 0#1
      let excl : (BitVec 1) := 0#1
      let at' : (BitVec 1) := 1#1
      let is_load : Bool := true
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure (()))


/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, t : Nat, t2 : Nat, k_tagchecked :
  Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_swp_128 (acquire : Bool) (n : Nat) (release : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 5018) 64) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescAtomicOp MemAtomicOp_SWP acquire release tagchecked) ) : SailM
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


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMGE_P_P_Z0__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5041)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) :
                SailM (BitVec esize) )
              let res ← (( do (undefined_bool_at (← occLabel 5042) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_EQ =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:635.59-635.60"
                    let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareEQ element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__3))
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:639.59-639.60"
                    let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__5))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:643.59-643.60"
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__7))
                | .Cmp_NE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:647.59-647.60"
                    let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareNE element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__9))
                | .Cmp_LT =>
                  (do
                    ArmFull.assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:651.117-651.118"
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0)) element
                      w__11))
                | .Cmp_LE =>
                  (do
                    ArmFull.assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:655.117-655.118"
                    let w__13 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0)) element
                      w__13))
                | _ => (pure (res)) ) : SailM Bool )
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


end ArmFull.Functions
