module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0087
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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ANDQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5726)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := (dtmp, result, stmp)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (dtmp, result, stmp) := loop_vars
        loop_vars ← do
          let dtmp : (BitVec esize) := (Sail.BitVec.castWidth (Ones (n := esize)))
          let (dtmp, stmp) ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (segments -i 1)
            (do
              let mut loop_vars_1 := (dtmp, stmp)
              for s in [loop_s_lower:loop_s_upper:1]i do
                let (dtmp, stmp) := loop_vars_1
                loop_vars_1 ← do
                  let w__2 ← (( do
                    (ActivePredicateElement mask ((s *i elempersegment) +i e) esize) ) : SailM Bool
                    )
                  if (w__2 : Bool)
                  then
                    (do
                      let w__3 ← (( do (Elem_read operand s 128) ) : SailM (BitVec 128) )
                      let stmp := (w__3 : (BitVec 128))
                      let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read stmp e esize)) ) :
                        SailM (BitVec esize) )
                      let dtmp := ((dtmp &&& w__4) : (BitVec esize))
                      (pure ((dtmp, stmp))))
                  else (pure ((dtmp, stmp)))
              (pure loop_vars_1)) ) : SailM ((BitVec esize) × (BitVec 128)) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb dtmp
                (Sail.Int.toNatChecked ((esize -i 1))) 0)))) ) : SailM (BitVec 128) )
          let result := (w__5 : (BitVec 128))
          (pure ((dtmp, result, stmp)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_EORQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5727)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := (dtmp, result, stmp)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (dtmp, result, stmp) := loop_vars
        loop_vars ← do
          let dtmp : (BitVec esize) := (Sail.BitVec.castWidth (Zeros (n := esize)))
          let (dtmp, stmp) ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (segments -i 1)
            (do
              let mut loop_vars_1 := (dtmp, stmp)
              for s in [loop_s_lower:loop_s_upper:1]i do
                let (dtmp, stmp) := loop_vars_1
                loop_vars_1 ← do
                  let w__2 ← (( do
                    (ActivePredicateElement mask ((s *i elempersegment) +i e) esize) ) : SailM Bool
                    )
                  if (w__2 : Bool)
                  then
                    (do
                      let w__3 ← (( do (Elem_read operand s 128) ) : SailM (BitVec 128) )
                      let stmp := (w__3 : (BitVec 128))
                      let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read stmp e esize)) ) :
                        SailM (BitVec esize) )
                      let dtmp := ((dtmp ^^^ w__4) : (BitVec esize))
                      (pure ((dtmp, stmp))))
                  else (pure ((dtmp, stmp)))
              (pure loop_vars_1)) ) : SailM ((BitVec esize) × (BitVec 128)) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb dtmp
                (Sail.Int.toNatChecked ((esize -i 1))) 0)))) ) : SailM (BitVec 128) )
          let result := (w__5 : (BitVec 128))
          (pure ((dtmp, result, stmp)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ORQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5728)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := (dtmp, result, stmp)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (dtmp, result, stmp) := loop_vars
        loop_vars ← do
          let dtmp : (BitVec esize) := (Sail.BitVec.castWidth (Zeros (n := esize)))
          let (dtmp, stmp) ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (segments -i 1)
            (do
              let mut loop_vars_1 := (dtmp, stmp)
              for s in [loop_s_lower:loop_s_upper:1]i do
                let (dtmp, stmp) := loop_vars_1
                loop_vars_1 ← do
                  let w__2 ← (( do
                    (ActivePredicateElement mask ((s *i elempersegment) +i e) esize) ) : SailM Bool
                    )
                  if (w__2 : Bool)
                  then
                    (do
                      let w__3 ← (( do (Elem_read operand s 128) ) : SailM (BitVec 128) )
                      let stmp := (w__3 : (BitVec 128))
                      let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read stmp e esize)) ) :
                        SailM (BitVec esize) )
                      let dtmp := ((dtmp ||| w__4) : (BitVec esize))
                      (pure ((dtmp, stmp))))
                  else (pure ((dtmp, stmp)))
              (pure loop_vars_1)) ) : SailM ((BitVec esize) × (BitVec 128)) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb dtmp
                (Sail.Int.toNatChecked ((esize -i 1))) 0)))) ) : SailM (BitVec 128) )
          let result := (w__5 : (BitVec 128))
          (pure ((dtmp, result, stmp)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADDQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_int_at (← occLabel 5729) ()) ) : SailM Int )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := (dtmp, result, stmp)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (dtmp, result, stmp) := loop_vars
        loop_vars ← do
          let dtmp : Int := 0
          let (dtmp, stmp) ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (segments -i 1)
            (do
              let mut loop_vars_1 := (dtmp, stmp)
              for s in [loop_s_lower:loop_s_upper:1]i do
                let (dtmp, stmp) := loop_vars_1
                loop_vars_1 ← do
                  let w__2 ← (( do
                    (ActivePredicateElement mask ((s *i elempersegment) +i e) esize) ) : SailM Bool
                    )
                  if (w__2 : Bool)
                  then
                    (do
                      let w__3 ← (( do (Elem_read operand s 128) ) : SailM (BitVec 128) )
                      let stmp := (w__3 : (BitVec 128))
                      let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read stmp e esize)) ) :
                        SailM (BitVec esize) )
                      let dtmp : Int := ((dtmp +i (BitVec.toNat w__4)) : Int)
                      (pure ((dtmp, stmp))))
                  else (pure ((dtmp, stmp)))
              (pure loop_vars_1)) ) : SailM (Int × (BitVec 128)) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
              (Sail.BitVec.castWidth (integer_subrange dtmp (esize -i 1) 0)))) ) : SailM
            (BitVec 128) )
          let result := (w__5 : (BitVec 128))
          (pure ((dtmp, result, stmp)))
      (pure loop_vars)) ) : SailM (Int × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMAXQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_int_at (← occLabel 5730) ()) ) : SailM Int )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := (dtmp, result, stmp)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (dtmp, result, stmp) := loop_vars
        loop_vars ← do
          let dtmp : Int :=
            if (is_unsigned : Bool)
            then 0
            else (Neg.neg (2 ^i (esize -i 1)))
          let (dtmp, stmp) ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (segments -i 1)
            (do
              let mut loop_vars_1 := (dtmp, stmp)
              for s in [loop_s_lower:loop_s_upper:1]i do
                let (dtmp, stmp) := loop_vars_1
                loop_vars_1 ← do
                  let w__2 ← (( do
                    (ActivePredicateElement mask ((s *i elempersegment) +i e) esize) ) : SailM Bool
                    )
                  if (w__2 : Bool)
                  then
                    (do
                      let w__3 ← (( do (Elem_read operand s 128) ) : SailM (BitVec 128) )
                      let stmp := (w__3 : (BitVec 128))
                      let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read stmp e esize)) ) :
                        SailM (BitVec esize) )
                      let dtmp : Int := ((Max.max dtmp (BitVec.toInt w__4)) : Int)
                      (pure ((dtmp, stmp))))
                  else (pure ((dtmp, stmp)))
              (pure loop_vars_1)) ) : SailM (Int × (BitVec 128)) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
              (Sail.BitVec.castWidth (integer_subrange dtmp (esize -i 1) 0)))) ) : SailM
            (BitVec 128) )
          let result := (w__5 : (BitVec 128))
          (pure ((dtmp, result, stmp)))
      (pure loop_vars)) ) : SailM (Int × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMAXQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_int_at (← occLabel 5731) ()) ) : SailM Int )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := (dtmp, result, stmp)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (dtmp, result, stmp) := loop_vars
        loop_vars ← do
          let dtmp : Int :=
            if (is_unsigned : Bool)
            then 0
            else (Neg.neg (2 ^i (esize -i 1)))
          let (dtmp, stmp) ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (segments -i 1)
            (do
              let mut loop_vars_1 := (dtmp, stmp)
              for s in [loop_s_lower:loop_s_upper:1]i do
                let (dtmp, stmp) := loop_vars_1
                loop_vars_1 ← do
                  let w__2 ← (( do
                    (ActivePredicateElement mask ((s *i elempersegment) +i e) esize) ) : SailM Bool
                    )
                  if (w__2 : Bool)
                  then
                    (do
                      let w__3 ← (( do (Elem_read operand s 128) ) : SailM (BitVec 128) )
                      let stmp := (w__3 : (BitVec 128))
                      let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read stmp e esize)) ) :
                        SailM (BitVec esize) )
                      let dtmp : Int := ((Max.max dtmp (BitVec.toNat w__4)) : Int)
                      (pure ((dtmp, stmp))))
                  else (pure ((dtmp, stmp)))
              (pure loop_vars_1)) ) : SailM (Int × (BitVec 128)) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
              (Sail.BitVec.castWidth (integer_subrange dtmp (esize -i 1) 0)))) ) : SailM
            (BitVec 128) )
          let result := (w__5 : (BitVec 128))
          (pure ((dtmp, result, stmp)))
      (pure loop_vars)) ) : SailM (Int × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMINQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_int_at (← occLabel 5732) ()) ) : SailM Int )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := (dtmp, result, stmp)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (dtmp, result, stmp) := loop_vars
        loop_vars ← do
          let dtmp : Int :=
            if (is_unsigned : Bool)
            then ((2 ^i esize) -i 1)
            else ((2 ^i (esize -i 1)) -i 1)
          let (dtmp, stmp) ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (segments -i 1)
            (do
              let mut loop_vars_1 := (dtmp, stmp)
              for s in [loop_s_lower:loop_s_upper:1]i do
                let (dtmp, stmp) := loop_vars_1
                loop_vars_1 ← do
                  let w__2 ← (( do
                    (ActivePredicateElement mask ((s *i elempersegment) +i e) esize) ) : SailM Bool
                    )
                  if (w__2 : Bool)
                  then
                    (do
                      let w__3 ← (( do (Elem_read operand s 128) ) : SailM (BitVec 128) )
                      let stmp := (w__3 : (BitVec 128))
                      let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read stmp e esize)) ) :
                        SailM (BitVec esize) )
                      let dtmp : Int := ((Min.min dtmp (BitVec.toInt w__4)) : Int)
                      (pure ((dtmp, stmp))))
                  else (pure ((dtmp, stmp)))
              (pure loop_vars_1)) ) : SailM (Int × (BitVec 128)) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
              (Sail.BitVec.castWidth (integer_subrange dtmp (esize -i 1) 0)))) ) : SailM
            (BitVec 128) )
          let result := (w__5 : (BitVec 128))
          (pure ((dtmp, result, stmp)))
      (pure loop_vars)) ) : SailM (Int × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMINQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let stmp : (BitVec 128) := (Zeros (n := 128))
  let dtmp ← (( do (undefined_int_at (← occLabel 5733) ()) ) : SailM Int )
  let (dtmp, result, stmp) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := (dtmp, result, stmp)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (dtmp, result, stmp) := loop_vars
        loop_vars ← do
          let dtmp : Int :=
            if (is_unsigned : Bool)
            then ((2 ^i esize) -i 1)
            else ((2 ^i (esize -i 1)) -i 1)
          let (dtmp, stmp) ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (segments -i 1)
            (do
              let mut loop_vars_1 := (dtmp, stmp)
              for s in [loop_s_lower:loop_s_upper:1]i do
                let (dtmp, stmp) := loop_vars_1
                loop_vars_1 ← do
                  let w__2 ← (( do
                    (ActivePredicateElement mask ((s *i elempersegment) +i e) esize) ) : SailM Bool
                    )
                  if (w__2 : Bool)
                  then
                    (do
                      let w__3 ← (( do (Elem_read operand s 128) ) : SailM (BitVec 128) )
                      let stmp := (w__3 : (BitVec 128))
                      let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read stmp e esize)) ) :
                        SailM (BitVec esize) )
                      let dtmp : Int := ((Min.min dtmp (BitVec.toNat w__4)) : Int)
                      (pure ((dtmp, stmp))))
                  else (pure ((dtmp, stmp)))
              (pure loop_vars_1)) ) : SailM (Int × (BitVec 128)) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
              (Sail.BitVec.castWidth (integer_subrange dtmp (esize -i 1) 0)))) ) : SailM
            (BitVec 128) )
          let result := (w__5 : (BitVec 128))
          (pure ((dtmp, result, stmp)))
      (pure loop_vars)) ) : SailM (Int × (BitVec 128) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ imm = 0 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMOV_Z_PI_B (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5734)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (PredicateElement operand e esize) ) : SailM (BitVec 1) )
          let result :=
            ((BitVec.update result (Sail.Int.toNatChecked (((elements *i imm) +i e))) (Bit w__0)) : (BitVec VL))
          (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ List.elem imm [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMOV_Z_PI_H (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5735)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    if ((imm == 0) : Bool)
    then
      (let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
      (pure (result)))
    else
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read d VL))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__1 ← (( do (PredicateElement operand e esize) ) : SailM (BitVec 1) )
          let result :=
            ((BitVec.update result (Sail.Int.toNatChecked (((elements *i imm) +i e))) (Bit w__1)) : (BitVec VL))
          (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ List.elem imm [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMOV_Z_PI_S (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5736)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    if ((imm == 0) : Bool)
    then
      (let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
      (pure (result)))
    else
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read d VL))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__1 ← (( do (PredicateElement operand e esize) ) : SailM (BitVec 1) )
          let result :=
            ((BitVec.update result (Sail.Int.toNatChecked (((elements *i imm) +i e))) (Bit w__1)) : (BitVec VL))
          (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
