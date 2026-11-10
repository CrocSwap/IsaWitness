import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0116
import ArmFull.Fn.M0178
import ArmFull.Fn.M0218
import ArmFull.Fn.M0227
import ArmFull.Fn.M0840
import ArmFull.Fn.M0924
import ArmFull.Fn.M1041
import ArmFull.Fn.M1071
import ArmFull.Fn.M1072

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

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_FMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) ) :
    SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6984)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 row esize))
                  ) : SailM (BitVec esize) )
                let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 col esize))
                  ) : SailM (BitVec esize) )
                let element3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row esize)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col esize))
                  else (pure false) ) : SailM Bool )
                if (w__2 : Bool)
                then
                  (do
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then
                        (do
                          (FPNeg element1))
                      else (pure (element1)) ) : SailM (BitVec esize) )
                    let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    let w__5 ← (( do (FPMulAdd_ZA element3 element1 element2 w__4) ) : SailM
                      (BitVec esize) )
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth w__5)))
                else
                  (do
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth element3)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 64 ∧
  List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_FMOPA_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) ) :
    SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6985)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 row esize))
                  ) : SailM (BitVec esize) )
                let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 col esize))
                  ) : SailM (BitVec esize) )
                let element3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row esize)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col esize))
                  else (pure false) ) : SailM Bool )
                if (w__2 : Bool)
                then
                  (do
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then
                        (do
                          (FPNeg element1))
                      else (pure (element1)) ) : SailM (BitVec esize) )
                    let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    let w__5 ← (( do (FPMulAdd_ZA element3 element1 element2 w__4) ) : SailM
                      (BitVec esize) )
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth w__5)))
                else
                  (do
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth element3)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 64 ∧
  List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_FMOPS_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) ) :
    SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6986)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 row esize))
                  ) : SailM (BitVec esize) )
                let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 col esize))
                  ) : SailM (BitVec esize) )
                let element3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row esize)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col esize))
                  else (pure false) ) : SailM Bool )
                if (w__2 : Bool)
                then
                  (do
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then
                        (do
                          (FPNeg element1))
                      else (pure (element1)) ) : SailM (BitVec esize) )
                    let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    let w__5 ← (( do (FPMulAdd_ZA element3 element1 element2 w__4) ) : SailM
                      (BitVec esize) )
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth w__5)))
                else
                  (do
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth element3)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_32 : Nat, m : Nat, n : Nat, k_sub_op
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_32 = (VL / 32 * (VL / 32 * 32)) -/
def execute_BFMOPA_ZA32_PP_ZZ__ (VL : Nat) (dim_dim_32 : Nat) (a : Nat) (b : Nat) (da : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da 32 dim_dim_32)) ) : SailM
    (BitVec dim_dim_32) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6987)
      (Sail.Int.toNatChecked (dim_dim_32)))) ) : SailM (BitVec dim_dim_32) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let prow_0 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 0) 16) ) : SailM
                  Bool )
                let prow_1 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 1) 16) ) : SailM
                  Bool )
                let pcol_0 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 0) 16) ) : SailM
                  Bool )
                let pcol_1 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 1) 16) ) : SailM
                  Bool )
                let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) 32) ) : SailM
                  (BitVec 32) )
                let sum ← (( do
                  if (((prow_0 && pcol_0) || (prow_1 && pcol_1)) : Bool)
                  then
                    (do
                      let erow_0 ← (( do
                        if (prow_0 : Bool)
                        then
                          (do
                            (Elem_read operand1 ((2 *i row) +i 0) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let erow_1 ← (( do
                        if (prow_1 : Bool)
                        then
                          (do
                            (Elem_read operand1 ((2 *i row) +i 1) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let ecol_0 ← (( do
                        if (pcol_0 : Bool)
                        then
                          (do
                            (Elem_read operand2 ((2 *i col) +i 0) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let ecol_1 ← (( do
                        if (pcol_1 : Bool)
                        then
                          (do
                            (Elem_read operand2 ((2 *i col) +i 1) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let (erow_0, erow_1) ← (( do
                        if (sub_op : Bool)
                        then
                          (do
                            let honor_altfp : Bool := false
                            let erow_0 ← (( do
                              if (prow_0 : Bool)
                              then
                                (do
                                  (BFNeg__1 (k_N := 16) erow_0 honor_altfp))
                              else (pure (erow_0)) ) : SailM (BitVec 16) )
                            let erow_1 ← (( do
                              if (prow_1 : Bool)
                              then
                                (do
                                  (BFNeg__1 (k_N := 16) erow_1 honor_altfp))
                              else (pure (erow_1)) ) : SailM (BitVec 16) )
                            (pure ((erow_0, erow_1))))
                        else (pure ((erow_0, erow_1))) ) : SailM ((BitVec 16) × (BitVec 16)) )
                      let w__10 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                      (BFDotAdd (k_N := 32) sum erow_0 erow_1 ecol_0 ecol_1 w__10))
                  else (pure (sum)) ) : SailM (BitVec 32) )
                (Elem_set result ((row *i dim) +i col) 32 sum)
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_32) )
  (ZAtile_set VL da 32 dim_dim_32 (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_32 : Nat, m : Nat, n : Nat, k_sub_op
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_32 = (VL / 32 * (VL / 32 * 32)) -/
def execute_BFMOPS_ZA32_PP_ZZ__ (VL : Nat) (dim_dim_32 : Nat) (a : Nat) (b : Nat) (da : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da 32 dim_dim_32)) ) : SailM
    (BitVec dim_dim_32) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6988)
      (Sail.Int.toNatChecked (dim_dim_32)))) ) : SailM (BitVec dim_dim_32) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let prow_0 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 0) 16) ) : SailM
                  Bool )
                let prow_1 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 1) 16) ) : SailM
                  Bool )
                let pcol_0 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 0) 16) ) : SailM
                  Bool )
                let pcol_1 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 1) 16) ) : SailM
                  Bool )
                let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) 32) ) : SailM
                  (BitVec 32) )
                let sum ← (( do
                  if (((prow_0 && pcol_0) || (prow_1 && pcol_1)) : Bool)
                  then
                    (do
                      let erow_0 ← (( do
                        if (prow_0 : Bool)
                        then
                          (do
                            (Elem_read operand1 ((2 *i row) +i 0) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let erow_1 ← (( do
                        if (prow_1 : Bool)
                        then
                          (do
                            (Elem_read operand1 ((2 *i row) +i 1) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let ecol_0 ← (( do
                        if (pcol_0 : Bool)
                        then
                          (do
                            (Elem_read operand2 ((2 *i col) +i 0) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let ecol_1 ← (( do
                        if (pcol_1 : Bool)
                        then
                          (do
                            (Elem_read operand2 ((2 *i col) +i 1) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let (erow_0, erow_1) ← (( do
                        if (sub_op : Bool)
                        then
                          (do
                            let honor_altfp : Bool := false
                            let erow_0 ← (( do
                              if (prow_0 : Bool)
                              then
                                (do
                                  (BFNeg__1 (k_N := 16) erow_0 honor_altfp))
                              else (pure (erow_0)) ) : SailM (BitVec 16) )
                            let erow_1 ← (( do
                              if (prow_1 : Bool)
                              then
                                (do
                                  (BFNeg__1 (k_N := 16) erow_1 honor_altfp))
                              else (pure (erow_1)) ) : SailM (BitVec 16) )
                            (pure ((erow_0, erow_1))))
                        else (pure ((erow_0, erow_1))) ) : SailM ((BitVec 16) × (BitVec 16)) )
                      let w__10 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                      (BFDotAdd (k_N := 32) sum erow_0 erow_1 ecol_0 ecol_1 w__10))
                  else (pure (sum)) ) : SailM (BitVec 32) )
                (Elem_set result ((row *i dim) +i col) 32 sum)
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_32) )
  (ZAtile_set VL da 32 dim_dim_32 (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_32 : Nat, m : Nat, n : Nat, k_sub_op
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_32 = (VL / 32 * (VL / 32 * 32)) -/
def execute_FMOPA_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_32 : Nat) (a : Nat) (b : Nat) (da : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da 32 dim_dim_32)) ) : SailM
    (BitVec dim_dim_32) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6989)
      (Sail.Int.toNatChecked (dim_dim_32)))) ) : SailM (BitVec dim_dim_32) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let prow_0 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 0) 16) ) : SailM
                  Bool )
                let prow_1 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 1) 16) ) : SailM
                  Bool )
                let pcol_0 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 0) 16) ) : SailM
                  Bool )
                let pcol_1 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 1) 16) ) : SailM
                  Bool )
                let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) 32) ) : SailM
                  (BitVec 32) )
                let sum ← (( do
                  if (((prow_0 && pcol_0) || (prow_1 && pcol_1)) : Bool)
                  then
                    (do
                      let erow_0 ← (( do
                        if (prow_0 : Bool)
                        then
                          (do
                            (Elem_read operand1 ((2 *i row) +i 0) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let erow_1 ← (( do
                        if (prow_1 : Bool)
                        then
                          (do
                            (Elem_read operand1 ((2 *i row) +i 1) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let ecol_0 ← (( do
                        if (pcol_0 : Bool)
                        then
                          (do
                            (Elem_read operand2 ((2 *i col) +i 0) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let ecol_1 ← (( do
                        if (pcol_1 : Bool)
                        then
                          (do
                            (Elem_read operand2 ((2 *i col) +i 1) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let (erow_0, erow_1) ← (( do
                        if (sub_op : Bool)
                        then
                          (do
                            let erow_0 ← (( do
                              if (prow_0 : Bool)
                              then
                                (do
                                  (FPNeg erow_0))
                              else (pure (erow_0)) ) : SailM (BitVec 16) )
                            let erow_1 ← (( do
                              if (prow_1 : Bool)
                              then
                                (do
                                  (FPNeg erow_1))
                              else (pure (erow_1)) ) : SailM (BitVec 16) )
                            (pure ((erow_0, erow_1))))
                        else (pure ((erow_0, erow_1))) ) : SailM ((BitVec 16) × (BitVec 16)) )
                      let w__10 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                      (FPDotAdd_ZA (k_N := 32) sum erow_0 erow_1 ecol_0 ecol_1 w__10))
                  else (pure (sum)) ) : SailM (BitVec 32) )
                (Elem_set result ((row *i dim) +i col) 32 sum)
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_32) )
  (ZAtile_set VL da 32 dim_dim_32 (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_32 : Nat, m : Nat, n : Nat, k_sub_op
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_32 = (VL / 32 * (VL / 32 * 32)) -/
def execute_FMOPS_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_32 : Nat) (a : Nat) (b : Nat) (da : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da 32 dim_dim_32)) ) : SailM
    (BitVec dim_dim_32) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6990)
      (Sail.Int.toNatChecked (dim_dim_32)))) ) : SailM (BitVec dim_dim_32) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let prow_0 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 0) 16) ) : SailM
                  Bool )
                let prow_1 ← (( do (ActivePredicateElement mask1 ((2 *i row) +i 1) 16) ) : SailM
                  Bool )
                let pcol_0 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 0) 16) ) : SailM
                  Bool )
                let pcol_1 ← (( do (ActivePredicateElement mask2 ((2 *i col) +i 1) 16) ) : SailM
                  Bool )
                let sum ← (( do (Elem_read operand3 ((row *i dim) +i col) 32) ) : SailM
                  (BitVec 32) )
                let sum ← (( do
                  if (((prow_0 && pcol_0) || (prow_1 && pcol_1)) : Bool)
                  then
                    (do
                      let erow_0 ← (( do
                        if (prow_0 : Bool)
                        then
                          (do
                            (Elem_read operand1 ((2 *i row) +i 0) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let erow_1 ← (( do
                        if (prow_1 : Bool)
                        then
                          (do
                            (Elem_read operand1 ((2 *i row) +i 1) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let ecol_0 ← (( do
                        if (pcol_0 : Bool)
                        then
                          (do
                            (Elem_read operand2 ((2 *i col) +i 0) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let ecol_1 ← (( do
                        if (pcol_1 : Bool)
                        then
                          (do
                            (Elem_read operand2 ((2 *i col) +i 1) 16))
                        else
                          (do
                            (FPZero 0#1 16)) ) : SailM (BitVec 16) )
                      let (erow_0, erow_1) ← (( do
                        if (sub_op : Bool)
                        then
                          (do
                            let erow_0 ← (( do
                              if (prow_0 : Bool)
                              then
                                (do
                                  (FPNeg erow_0))
                              else (pure (erow_0)) ) : SailM (BitVec 16) )
                            let erow_1 ← (( do
                              if (prow_1 : Bool)
                              then
                                (do
                                  (FPNeg erow_1))
                              else (pure (erow_1)) ) : SailM (BitVec 16) )
                            (pure ((erow_0, erow_1))))
                        else (pure ((erow_0, erow_1))) ) : SailM ((BitVec 16) × (BitVec 16)) )
                      let w__10 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                      (FPDotAdd_ZA (k_N := 32) sum erow_0 erow_1 ecol_0 ecol_1 w__10))
                  else (pure (sum)) ) : SailM (BitVec 32) )
                (Elem_set result ((row *i dim) +i col) 32 sum)
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_32) )
  (ZAtile_set VL da 32 dim_dim_32 (Sail.BitVec.castWidth result))


end ArmFull.Functions
