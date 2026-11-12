import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0118
import ArmFull.Fn.M0120
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ index ∧
  index ≤ 63 ∧ List.elem esize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_DUP_Z_Zi__ (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5404)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element ← (( do
    if ((index ≥b elements) : Bool)
    then
      (let element : (BitVec esize) := (Sail.BitVec.castWidth (Zeros (n := esize)))
      (pure (element)))
    else
      (do
        ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 index esize))) ) : SailM (BitVec esize) )
  let result : (BitVec VL) :=
    (Sail.BitVec.castWidth (BitVec.replicateBits element
      (Sail.Int.toNatChecked ((Int.ediv VL esize)))))
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_DUP_Z_R__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let operand ← (( do (undefined_bitvector_at (← occLabel 5406) 64) ) : SailM (BitVec 64) )
  let operand ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5407)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          (Elem_set result e esize
            (Sail.BitVec.castWidth (Sail.BitVec.extractLsb operand
              (Sail.Int.toNatChecked ((esize -i 1))) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_isBefore : Bool, n : Nat, rsize :
  Nat, List.elem rsize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LASTA_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (n : Nat) (rsize : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let last : Int :=
    if (isBefore : Bool)
    then
      (if ((last <b 0) : Bool)
      then (elements -i 1)
      else last)
    else
      (let last : Int := (last +i 1)
      if ((last ≥b elements) : Bool)
      then 0
      else last)
  let last : Int := last
  ArmFull.assert (rsize ≥b esize) "sail-arm/instrs64_sve.sail:28256.39-28256.40"
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand last esize)) ) : SailM
    (BitVec esize) )
  let result : (BitVec rsize) := (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend w__0 rsize))
  (X_set d rsize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_isBefore : Bool, n : Nat, rsize :
  Nat, List.elem rsize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LASTB_R_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (n : Nat) (rsize : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let last : Int :=
    if (isBefore : Bool)
    then
      (if ((last <b 0) : Bool)
      then (elements -i 1)
      else last)
    else
      (let last : Int := (last +i 1)
      if ((last ≥b elements) : Bool)
      then 0
      else last)
  let last : Int := last
  ArmFull.assert (rsize ≥b esize) "sail-arm/instrs64_sve.sail:28329.39-28329.40"
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand last esize)) ) : SailM
    (BitVec esize) )
  let result : (BitVec rsize) := (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend w__0 rsize))
  (X_set d rsize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_isBefore : Bool, n : Nat, 0 ≤ n
  ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LASTA_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let last : Int :=
    if (isBefore : Bool)
    then
      (if ((last <b 0) : Bool)
      then (elements -i 1)
      else last)
    else
      (let last : Int := (last +i 1)
      if ((last ≥b elements) : Bool)
      then 0
      else last)
  let last : Int := last
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand last esize)) ) : SailM
    (BitVec esize) )
  (V_set d esize (Sail.BitVec.castWidth w__0))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_isBefore : Bool, n : Nat, 0 ≤ n
  ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LASTB_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let last : Int :=
    if (isBefore : Bool)
    then
      (if ((last <b 0) : Bool)
      then (elements -i 1)
      else last)
    else
      (let last : Int := (last +i 1)
      if ((last ≥b elements) : Bool)
      then 0
      else last)
  let last : Int := last
  let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand last esize)) ) : SailM
    (BitVec esize) )
  (V_set d esize (Sail.BitVec.castWidth w__0))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PUNPKLO_P_P__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5408)
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
          let pbit ← (( do
            (PredicateElement operand
              (if (hi : Bool)
              then (e +i elements)
              else e) (Int.ediv esize 2)) ) : SailM (BitVec 1) )
          (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PUNPKHI_P_P__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5409)
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
          let pbit ← (( do
            (PredicateElement operand
              (if (hi : Bool)
              then (e +i elements)
              else e) (Int.ediv esize 2)) ) : SailM (BitVec 1) )
          (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, swsize : Nat, swsize = 32
  ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_REVW_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (swsize : Nat) : SailM Unit := do
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
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
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
              let w__3 ← (( do (Reverse element swsize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__3)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, swsize : Nat, swsize = 16
  ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_REVH_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (swsize : Nat) : SailM Unit := do
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
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
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
              let w__3 ← (( do (Reverse element swsize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__3)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, swsize : Nat, swsize = 8 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_REVB_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (swsize : Nat) : SailM Unit := do
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
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
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
              let w__3 ← (( do (Reverse element swsize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__3)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, k_is_unsigned : Bool, n : Nat, 0
  ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UUNPKLO_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let hsize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 2)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5410)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do
            if (hi : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (Elem_read operand (e +i elements) hsize)))
            else
              (do
                ((Sail.BitVec.castWidth ) <$> (Elem_read operand e hsize))) ) : SailM
            (BitVec (Sail.Int.toNatChecked hsize)) )
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend element esize is_unsigned)) ) :
            SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, k_is_unsigned : Bool, n : Nat, 0
  ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UUNPKHI_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let hsize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 2)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5411)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do
            if (hi : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (Elem_read operand (e +i elements) hsize)))
            else
              (do
                ((Sail.BitVec.castWidth ) <$> (Elem_read operand e hsize))) ) : SailM
            (BitVec (Sail.Int.toNatChecked hsize)) )
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend element esize is_unsigned)) ) :
            SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, k_is_unsigned : Bool, n : Nat, 0
  ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SUNPKLO_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let hsize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 2)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5412)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do
            if (hi : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (Elem_read operand (e +i elements) hsize)))
            else
              (do
                ((Sail.BitVec.castWidth ) <$> (Elem_read operand e hsize))) ) : SailM
            (BitVec (Sail.Int.toNatChecked hsize)) )
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend element esize is_unsigned)) ) :
            SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, k_is_unsigned : Bool, n : Nat, 0
  ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SUNPKHI_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let hsize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 2)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5413)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do
            if (hi : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (Elem_read operand (e +i elements) hsize)))
            else
              (do
                ((Sail.BitVec.castWidth ) <$> (Elem_read operand e hsize))) ) : SailM
            (BitVec (Sail.Int.toNatChecked hsize)) )
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend element esize is_unsigned)) ) :
            SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_setflags : Bool, List.elem esize
  [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PTRUE_P_S__ (VL : Nat) (d : Nat) (esize : Nat) (pat : (BitVec 5)) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5414)
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
          let pbit : (BitVec 1) :=
            if ((e <b count) : Bool)
            then 1#1
            else 0#1
          (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest result result esize) ) : SailM (BitVec 4) )
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_setflags : Bool, List.elem esize
  [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PTRUES_P_S__ (VL : Nat) (d : Nat) (esize : Nat) (pat : (BitVec 5)) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5415)
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
          let pbit : (BitVec 1) :=
            if ((e <b count) : Bool)
            then 1#1
            else 0#1
          (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest result result esize) ) : SailM (BitVec 4) )
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PFALSE_P__ (VL : Nat) (d : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  (P_set d PL (Sail.BitVec.castWidth (Zeros (n := PL))))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_PTEST__P_P__ (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__0 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with V := (Sail.BitVec.extractLsb split_vec 0 0) }


end ArmFull.Functions
