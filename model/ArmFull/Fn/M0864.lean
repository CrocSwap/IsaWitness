import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
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

/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECW_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5340)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_UQDECD_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5341)
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
def execute_SQDECB_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5342)
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
def execute_SQDECH_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5343)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECW_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5344)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, ssize : Nat, ssize =
  64 ∧ 1 ≤ imm ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 -/
def execute_SQDECD_R_RS_X (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (ssize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn ssize)) ) : SailM (BitVec ssize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5345)
      (Sail.Int.toNatChecked (ssize)))) ) : SailM (BitVec ssize) )
  let element1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ (element1 -i (count *i imm)) ssize
      is_unsigned)) ) : SailM ((BitVec ssize) × Bool) )
  let result : (BitVec ssize) := __tup_0
  let w__0 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
  (X_set dn 64 w__0)


/-- Type quantifiers: d : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_CNTB_R_S__ (d : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  (X_set d 64 (integer_subrange (count *i imm) 63 0))


/-- Type quantifiers: d : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_CNTH_R_S__ (d : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  (X_set d 64 (integer_subrange (count *i imm) 63 0))


/-- Type quantifiers: d : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_CNTW_R_S__ (d : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  (X_set d 64 (integer_subrange (count *i imm) 63 0))


/-- Type quantifiers: d : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_CNTD_R_S__ (d : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  (X_set d 64 (integer_subrange (count *i imm) 63 0))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECH_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5346)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.subInt w__0 (count *i imm))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECW_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5347)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.subInt w__0 (count *i imm))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_DECD_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5348)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.subInt w__0 (count *i imm))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCH_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5349)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.addInt w__0 (count *i imm))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCW_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5350)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.addInt w__0 (count *i imm))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, 1 ≤ imm ∧
  imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_INCD_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5351)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.addInt w__0 (count *i imm))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm
  ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQINCH_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5352)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (element1 +i (count *i imm)) esize is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm
  ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQINCW_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5353)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (element1 +i (count *i imm)) esize is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm
  ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQINCD_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5354)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (element1 +i (count *i imm)) esize is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm
  ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQINCH_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5355)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (element1 +i (count *i imm)) esize is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm
  ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQINCW_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5356)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (element1 +i (count *i imm)) esize is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm
  ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQINCD_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5357)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (element1 +i (count *i imm)) esize is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm
  ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQDECH_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5358)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (element1 -i (count *i imm)) esize is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm
  ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQDECW_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5359)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (element1 -i (count *i imm)) esize is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm
  ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UQDECD_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5360)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (element1 -i (count *i imm)) esize is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm
  ∧ imm ≤ 16 ∧ esize = 16 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQDECH_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5361)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (element1 -i (count *i imm)) esize is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm
  ∧ imm ≤ 16 ∧ esize = 32 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQDECW_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5362)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (element1 -i (count *i imm)) esize is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, k_is_unsigned : Bool, 1 ≤ imm
  ∧ imm ≤ 16 ∧ esize = 64 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SQDECD_Z_ZS__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (pat : (BitVec 5)) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5363)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let (__tup_0, _) ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (element1 -i (count *i imm)) esize is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
          (Elem_set result e esize (Sail.BitVec.castWidth __tup_0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
