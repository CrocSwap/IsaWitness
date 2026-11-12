import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0115
import ArmFull.Fn.M0144
import ArmFull.Fn.M0150
import ArmFull.Fn.M0159
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203

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

/-- Type quantifiers: d : Nat, lsbit : Nat, msbit : Nat, 0 ≤ msbit ∧
  msbit ≤ 31 ∧ 0 ≤ lsbit ∧ lsbit ≤ 31 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_BFC_Op_A_txt (d : Nat) (lsbit : Nat) (msbit : Nat) : SailM Unit := do
  ArmFull.assert (lsbit ≤b msbit) "sail-arm/instrs32.sail:1519.39-1519.40"
  let w__0 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d
    (Sail.BitVec.castWidth (Sail.BitVec.updateSubrange w__0 msbit lsbit
      (Sail.BitVec.castWidth (BitVec.replicateBits 0#1
        (Sail.Int.toNatChecked (((msbit -i lsbit) +i 1))))))))


/-- Type quantifiers: d : Nat, lsbit : Nat, msbit : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ msbit ∧ msbit ≤ 31 ∧ 0 ≤ lsbit ∧ lsbit ≤ 31 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_BFI_Op_A_txt (d : Nat) (lsbit : Nat) (msbit : Nat) (n : Nat) : SailM Unit := do
  ArmFull.assert (0 ≤b (msbit -i lsbit)) "sail-arm/instrs32.sail:1587.43-1587.44"
  let w__0 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  (R_set d
    (Sail.BitVec.castWidth (Sail.BitVec.updateSubrange w__0 msbit lsbit
      (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1 (Sail.Int.toNatChecked ((msbit -i lsbit)))
        0)))))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_BIC_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 2979) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 2980) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (Shift_C w__1 shift_t shift_n w__2.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__3 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__4 &&& (Complement.complement shifted))
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with Z := (IsZeroBit result) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_CLZ_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result : Int := (CountLeadingZeroBits w__0)
  (R_set d (integer_subrange result 31 0))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_CMN_i_Op_A_txt (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2983) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2984) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) := ((AddWithCarry w__0 imm32 0#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb nzcv 0 0) }


/-- Type quantifiers: m : Nat, n : Nat, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_CMN_r_Op_A_txt (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2985) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2986) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) := ((AddWithCarry w__2 shifted 0#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb nzcv 0 0) }


/-- Type quantifiers: m : Nat, n : Nat, s : Nat, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_CMN_rr_Op_A_txt (m : Nat) (n : Nat) (s : Nat) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2993) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2994) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__1 shift_t shift_n w__2.C) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) := ((AddWithCarry w__3 shifted 0#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb nzcv 0 0) }


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_CMP_i_Op_A_txt (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2995) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2996) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) :=
    ((AddWithCarry w__0 (Complement.complement imm32) 1#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb nzcv 0 0) }


/-- Type quantifiers: m : Nat, n : Nat, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_CMP_r_Op_A_txt (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2997) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2998) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) :=
    ((AddWithCarry w__2 (Complement.complement shifted) 1#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb nzcv 0 0) }


/-- Type quantifiers: m : Nat, n : Nat, s : Nat, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_CMP_rr_Op_A_txt (m : Nat) (n : Nat) (s : Nat) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3007) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3008) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__1 shift_t shift_n w__2.C) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) :=
    ((AddWithCarry w__3 (Complement.complement shifted) 1#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb nzcv 0 0) }


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_EOR_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3026) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 3027) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (Shift_C w__1 shift_t shift_n w__2.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__3 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__4 ^^^ shifted)
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with Z := (IsZeroBit result) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, List.elem m
  [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_LSL_i_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3100) 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3101) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (Shift_C w__0 SRType_LSL shift_n w__1.C) ) : SailM ((BitVec 32) × (BitVec 1))
    )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
  let result : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with Z := (IsZeroBit result) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_LSL_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3103) 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3104) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (Shift_C w__1 SRType_LSL shift_n w__2.C) ) : SailM ((BitVec 32) × (BitVec 1))
    )
  let (tup__0, tup__1) := (w__3 : ((BitVec 32) × (BitVec 1)))
  let result : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, List.elem m
  [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_LSR_i_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3105) 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3106) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (Shift_C w__0 SRType_LSR shift_n w__1.C) ) : SailM ((BitVec 32) × (BitVec 1))
    )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
  let result : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with Z := (IsZeroBit result) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, List.elem n
  [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_LSR_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3108) 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3109) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (Shift_C w__1 SRType_LSR shift_n w__2.C) ) : SailM ((BitVec 32) × (BitVec 1))
    )
  let (tup__0, tup__1) := (w__3 : ((BitVec 32) × (BitVec 1)))
  let result : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := carry })
  else (pure (()))


/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_MLA_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let operand1 : Int := (BitVec.toInt w__0)
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let operand2 : Int := (BitVec.toInt w__1)
  let w__2 ← (( do (R_read a) ) : SailM (BitVec 32) )
  let addend : Int := (BitVec.toInt w__2)
  let result : Int := ((operand1 *i operand2) +i addend)
  (R_set d (integer_subrange result 31 0))
  if (setflags : Bool)
  then
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with N := (BitVec.setWidth 1 (BitVec.join1 [(integer_access result 31)])) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with Z := (IsZeroBit (integer_subrange result 31 0)) })
  else (pure (()))


/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_MLS_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let operand1 : Int := (BitVec.toInt w__0)
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let operand2 : Int := (BitVec.toInt w__1)
  let w__2 ← (( do (R_read a) ) : SailM (BitVec 32) )
  let addend : Int := (BitVec.toInt w__2)
  let result : Int := (addend -i (operand1 *i operand2))
  (R_set d (integer_subrange result 31 0))


/-- Type quantifiers: d : Nat, m : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MOV_rr_Op_A_txt (d : Nat) (m : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3126) 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3127) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (Shift_C w__1 shift_t shift_n w__2.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__3 : ((BitVec 32) × (BitVec 1)))
  let result : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MOVT_Op_A_txt (d : Nat) (imm16 : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__0 31 16 imm16))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MUL_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let operand1 : Int := (BitVec.toInt w__0)
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let operand2 : Int := (BitVec.toInt w__1)
  let result : Int := (operand1 *i operand2)
  (R_set d (integer_subrange result 31 0))
  if (setflags : Bool)
  then
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with N := (BitVec.setWidth 1 (BitVec.join1 [(integer_access result 31)])) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with Z := (IsZeroBit (integer_subrange result 31 0)) })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MVN_rr_Op_A_txt (d : Nat) (m : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3140) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 3141) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (Shift_C w__1 shift_t shift_n w__2.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__3 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let result : (BitVec 32) := (Complement.complement shifted)
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ORN_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__0 ||| (Complement.complement imm32))
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Z := (IsZeroBit result) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ORN_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3144) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 3145) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (Shift_C w__0 shift_t shift_n w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__3 ||| (Complement.complement shifted))
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ORR_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3160) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 3161) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (Shift_C w__1 shift_t shift_n w__2.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__3 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__4 ||| shifted)
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with Z := (IsZeroBit result) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, shift_n : Int, k_tbform : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_PKH_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (tbform : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let operand2 ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__4 ← (( do
    if (tbform : Bool)
    then (pure ((Sail.BitVec.extractLsb operand2 15 0)))
    else
      (do
        let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__3 15 0)))) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__2 15 0 w__4))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__7 ← (( do
    if (tbform : Bool)
    then
      (do
        let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__6 31 16))))
    else (pure ((Sail.BitVec.extractLsb operand2 31 16))) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 w__7))


/-- Type quantifiers: k_add : Bool, k_is_pldw : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_PLD_i_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (is_pldw : Bool) (n : Nat) : SailM Unit := do
  let address ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__0 + imm32))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__1 - imm32)))) ) : SailM (BitVec 32) )
  (pure (if (is_pldw : Bool)
    then (Hint_PreloadDataForWrite address)
    else (Hint_PreloadData address)))


/-- Type quantifiers: k_add : Bool, k_is_pldw : Bool, m : Nat, n : Nat, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_PLD_r_Op_A_txt (add : Bool) (is_pldw : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let offset ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let address ← (( do
    if (add : Bool)
    then
      (do
        let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__2 + offset))))
    else
      (do
        let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__3 - offset)))) ) : SailM (BitVec 32) )
  (pure (if (is_pldw : Bool)
    then (Hint_PreloadDataForWrite address)
    else (Hint_PreloadData address)))


/-- Type quantifiers: k_add : Bool, m : Nat, n : Nat, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_PLI_r_Op_A_txt (add : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let offset ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let address ← (( do
    if (add : Bool)
    then
      (do
        let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__2 + offset))))
    else
      (do
        let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__3 - offset)))) ) : SailM (BitVec 32) )
  (pure ((Hint_PreloadInstr address)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QADD16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__0 15 0)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__1 15 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 31 16)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__3 31 16)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__5 ← (( do (SignedSat sum1 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 w__5))
  let w__6 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__7 ← (( do (SignedSat sum2 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__6 31 16 w__7))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QADD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__0 7 0)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__1 7 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 15 8)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__3 15 8)))
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum3 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__4 23 16)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__5 23 16)))
  let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum4 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__6 31 24)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__7 31 24)))
  let w__8 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__9 ← (( do (SignedSat sum1 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__8 7 0 w__9))
  let w__10 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__11 ← (( do (SignedSat sum2 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__10 15 8 w__11))
  let w__12 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__13 ← (( do (SignedSat sum3 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__12 23 16 w__13))
  let w__14 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__15 ← (( do (SignedSat sum4 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__14 31 24 w__15))


end ArmFull.Functions
