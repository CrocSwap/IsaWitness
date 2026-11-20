module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M1050
public import ArmFull.Fn.M1092
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1123 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNMP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5132)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5133)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let w__3 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__3 : (BitVec esize))
                    let w__4 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__4 : (BitVec esize))
                    (pure ((element1, element2))))
                else
                  (do
                    let w__5 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e -i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__5 : (BitVec esize))
                    let w__6 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__6 : (BitVec esize))
                    (pure ((element1, element2)))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:8960.53-8960.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMinNum element1 element2 w__7) ) : SailM (BitVec esize) )
              let w__9 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__8)) ) : SailM
                (BitVec VL) )
              let result := (w__9 : (BitVec VL))
              (pure ((element1, element2, result))))
          else (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINP_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5134)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5135)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let (element1, element2) ← (( do
                if ((IsEven e) : Bool)
                then
                  (do
                    let w__3 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__3 : (BitVec esize))
                    let w__4 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (e +i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__4 : (BitVec esize))
                    (pure ((element1, element2))))
                else
                  (do
                    let w__5 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e -i 1) esize)) ) : SailM
                      (BitVec esize) )
                    let element1 := (w__5 : (BitVec esize))
                    let w__6 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (e +i 0) esize)) ) : SailM
                      (BitVec esize) )
                    let element2 := (w__6 : (BitVec esize))
                    (pure ((element1, element2)))) ) : SailM ((BitVec esize) × (BitVec esize)) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:9038.53-9038.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMin element1 element2 w__7) ) : SailM (BitVec esize) )
              let w__9 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__8)) ) : SailM
                (BitVec VL) )
              let result := (w__9 : (BitVec VL))
              (pure ((element1, element2, result))))
          else (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n
  ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLALB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5136)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i 0)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i 0)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
            SailM (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) (Sail.BitVec.castWidth element3)
              (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__1)) ) : SailM
            (BitVec 32) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n
  ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLALT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5137)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i 1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i 1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
            SailM (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) (Sail.BitVec.castWidth element3)
              (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__1)) ) : SailM
            (BitVec 32) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n
  ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSLB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5138)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i 0)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i 0)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
            SailM (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) (Sail.BitVec.castWidth element3)
              (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__1)) ) : SailM
            (BitVec 32) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n
  ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSLT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5139)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i 1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i 1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
            SailM (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) (Sail.BitVec.castWidth element3)
              (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__1)) ) : SailM
            (BitVec 32) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg :
  Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLALB_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5140)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := ((2 *i segmentbase) +i index)
          let element1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i 0)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
            SailM (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) (Sail.BitVec.castWidth element3)
              (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__1)) ) : SailM
            (BitVec 32) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg :
  Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLALT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5141)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := ((2 *i segmentbase) +i index)
          let element1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i 1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
            SailM (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) (Sail.BitVec.castWidth element3)
              (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__1)) ) : SailM
            (BitVec 32) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg :
  Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSLB_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5142)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := ((2 *i segmentbase) +i index)
          let element1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i 0)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
            SailM (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) (Sail.BitVec.castWidth element3)
              (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__1)) ) : SailM
            (BitVec 32) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg :
  Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLSLT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5143)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := ((2 *i segmentbase) +i index)
          let element1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i 1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
            SailM (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec (esize / 2)) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPMulAddH (k_N := 32) (Sail.BitVec.castWidth element3)
              (Sail.BitVec.castWidth element1) (Sail.BitVec.castWidth element2) w__1)) ) : SailM
            (BitVec 32) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLALB_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5144)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
          let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (BFMulAddH (k_N := 32) element3 element1 element2 w__0) ) : SailM
            (BitVec 32) )
          (Elem_set result e 32 w__1)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLALT_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5145)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
          let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (BFMulAddH (k_N := 32) element3 element1 element2 w__0) ) : SailM
            (BitVec 32) )
          (Elem_set result e 32 w__1)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, k_op1_neg : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLSLB_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5146)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
          let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (BFNeg (k_N := 16) element1))
            else (pure (element1)) ) : SailM (BitVec 16) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do (BFMulAddH (k_N := 32) element3 element1 element2 w__1) ) : SailM
            (BitVec 32) )
          (Elem_set result e 32 w__2)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
