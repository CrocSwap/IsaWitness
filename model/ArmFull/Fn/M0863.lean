import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840

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

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧
  m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQDECP_Z_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5312)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element -i count) esize
              is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, 0 ≤ m ∧
  m ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQDECP_Z_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5313)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let count : Int := 0
  let count ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := count
      for e in [loop_e_lower:loop_e_upper:1]i do
        let count := loop_vars
        loop_vars ← do
          let w__0 ← (( do (ActivePredicateElement operand2 e esize) ) : SailM Bool )
          let count : Int :=
            if (w__0 : Bool)
            then (count +i 1)
            else count
          (pure (count))
      (pure loop_vars)) ) : SailM Int )
  let count : Int := count
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element -i count) esize
              is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECB_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let VL : Nat := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.subInt operand1 (count *i imm)))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECH_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let VL : Nat := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.subInt operand1 (count *i imm)))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECW_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let VL : Nat := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.subInt operand1 (count *i imm)))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECD_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let VL : Nat := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.subInt operand1 (count *i imm)))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCB_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let VL : Nat := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.addInt operand1 (count *i imm)))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCH_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let VL : Nat := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.addInt operand1 (count *i imm)))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCW_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let VL : Nat := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.addInt operand1 (count *i imm)))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCD_R_RS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let VL : Nat := VL
  let operand1 ← (( do (X_read dn 64) ) : SailM (BitVec 64) )
  (X_set dn 64 (BitVec.addInt operand1 (count *i imm)))


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCB_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5314)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCH_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5315)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCW_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5316)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCD_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5317)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCB_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5318)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCH_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5319)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCW_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5320)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCD_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5321)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCB_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5322)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCH_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5323)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCW_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5324)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQINCD_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5325)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCB_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5326)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCH_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5327)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCW_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5328)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQINCD_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5329)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 +i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECB_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5330)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECH_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5331)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECW_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5332)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECD_R_RS_UW (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5333)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECB_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5334)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECH_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5335)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECW_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5336)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  32 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECD_R_RS_SX (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5337)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECB_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5338)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECH_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5339)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


end ArmFull.Functions
