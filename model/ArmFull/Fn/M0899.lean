module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0120
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0866 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: VL : Nat, dst : Nat, esize : Nat, position__arg : Nat, s1 : Nat, s2 : Nat, 0
  ≤ s2 ∧
  s2 ≤ 31 ∧
  0 ≤ s1 ∧
  s1 ≤ 31 ∧
  0 ≤ position__arg ∧
  position__arg ≤ 255 ∧ esize = 8 ∧ 0 ≤ dst ∧ dst ≤ 31 ∧ (is_VL VL) -/
def execute_EXT_Z_ZI_Des (VL : Nat) (dst : Nat) (esize : Nat) (position__arg : Nat) (s1 : Nat) (s2 : Nat) : SailM Unit := do
  let position : Int := position__arg
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read s1 VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read s2 VL)) ) : SailM (BitVec VL) )
  let position : Int :=
    if ((position ≥b elements) : Bool)
    then 0
    else position
  let position : Int := (Int.shiftl position 3)
  let concat : (BitVec (VL * 2)) := (Sail.BitVec.castWidth (operand2 +++ operand1))
  ArmFull.assert ((0 ≤b (Sail.Int.toNatChecked (position))) && ((((Sail.Int.toNatChecked (position)) +i VL) -i 1) <b (VL *i 2))) "sail-inputs/16-instrs64_sve.sail:27842.71-27842.72"
  let result : (BitVec VL) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb concat
      (Sail.Int.toNatChecked ((((Sail.Int.toNatChecked (position)) +i VL) -i 1)))
      (Sail.Int.toNatChecked ((Sail.Int.toNatChecked (position))))))
  (Z_set dst VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dst : Nat, esize : Nat, position__arg : Nat, s1 : Nat, s2 : Int, 0
  ≤ s1 ∧
  s1 ≤ 31 ∧
  0 ≤ position__arg ∧
  position__arg ≤ 255 ∧ esize = 8 ∧ 0 ≤ dst ∧ dst ≤ 31 ∧ (is_VL VL) -/
def execute_EXT_Z_ZI_Con (VL : Nat) (dst : Nat) (esize : Nat) (position__arg : Nat) (s1 : Nat) (s2 : Int) : SailM Unit := do
  let position : Int := position__arg
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read s1 VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read s2 VL)) ) : SailM (BitVec VL) )
  let position : Int :=
    if ((position ≥b elements) : Bool)
    then 0
    else position
  let position : Int := (Int.shiftl position 3)
  let concat : (BitVec (VL * 2)) := (Sail.BitVec.castWidth (operand2 +++ operand1))
  ArmFull.assert ((0 ≤b (Sail.Int.toNatChecked (position))) && ((((Sail.Int.toNatChecked (position)) +i VL) -i 1) <b (VL *i 2))) "sail-inputs/16-instrs64_sve.sail:27905.71-27905.72"
  let result : (BitVec VL) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb concat
      (Sail.Int.toNatChecked ((((Sail.Int.toNatChecked (position)) +i VL) -i 1)))
      (Sail.Int.toNatChecked ((Sail.Int.toNatChecked (position))))))
  (Z_set dst VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CPY_Z_P_R__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let result ← (( do
    if (w__0 : Bool)
    then
      (do
        let operand1 ← (( do (undefined_bitvector_at (← occLabel 5403) 64) ) : SailM (BitVec 64)
          )
        let operand1 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars
            loop_vars ← do
              let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
              if (w__3 : Bool)
              then
                (do
                  (Elem_set result e esize
                    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb operand1
                      (Sail.Int.toNatChecked ((esize -i 1))) 0))))
              else (pure (result))
          (pure loop_vars)))
    else (pure (result)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CPY_Z_P_V__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (V_read n esize)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := esize))))) ) : SailM (BitVec esize) )
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
              (Elem_set result e esize (Sail.BitVec.castWidth operand1)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


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
  ArmFull.assert (rsize ≥b esize) "sail-inputs/16-instrs64_sve.sail:28256.39-28256.40"
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
  ArmFull.assert (rsize ≥b esize) "sail-inputs/16-instrs64_sve.sail:28329.39-28329.40"
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


end ArmFull.Functions
