import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0218
import ArmFull.Fn.M0227
import ArmFull.Fn.M0840
import ArmFull.Fn.M0849

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
def execute_BMOPA_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7548)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 row esize)) ) :
            SailM (BitVec esize) )
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
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
                    let res : Int := (BitCount (Complement.complement (element1 ^^^ element2)))
                    let res : Int :=
                      if (sub_op : Bool)
                      then (Neg.neg res)
                      else res
                    let res : Int := res
                    (Elem_set result ((row *i dim) +i col) esize
                      (Sail.BitVec.castWidth (BitVec.addInt element3 res))))
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
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_BMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7549)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 row esize)) ) :
            SailM (BitVec esize) )
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
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
                    let res : Int := (BitCount (Complement.complement (element1 ^^^ element2)))
                    let res : Int :=
                      if (sub_op : Bool)
                      then (Neg.neg res)
                      else res
                    let res : Int := res
                    (Elem_set result ((row *i dim) +i col) esize
                      (Sail.BitVec.castWidth (BitVec.addInt element3 res))))
                else
                  (do
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth element3)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, k_is_unsigned
  : Bool, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SMOPA_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7550)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7551) ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := (prod, result)
      for row in [loop_row_lower:loop_row_upper:1]i do
        let (prod, result) := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := (prod, result)
            for col in [loop_col_lower:loop_col_upper:1]i do
              let (prod, result) := loop_vars_1
              loop_vars_1 ← do
                let sum ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let (prod, sum) ← (( do
                  let loop_k_lower : Nat := 0
                  let loop_k_upper : Nat := 1
                  (do
                    let mut loop_vars_2 := (prod, sum)
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let (prod, sum) := loop_vars_2
                      loop_vars_2 ← do
                        let w__2 ← (( do
                          if ((← do
                               (ActivePredicateElement mask1 ((2 *i row) +i k) (Int.ediv esize 2))) : Bool)
                          then
                            (do
                              (ActivePredicateElement mask2 ((2 *i col) +i k) (Int.ediv esize 2)))
                          else (pure false) ) : SailM Bool )
                        if (w__2 : Bool)
                        then
                          (do
                            let w__3 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i row) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                              (BitVec (esize / 2)) )
                            let w__4 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
                            let w__5 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i col) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                              (BitVec (esize / 2)) )
                            let w__6 ← (( do (asl_Int w__5 is_unsigned) ) : SailM Int )
                            let prod : Int := ((w__4 *i w__6) : Int)
                            let prod : Int :=
                              if (sub_op : Bool)
                              then (Neg.neg prod)
                              else prod
                            let sum : (BitVec esize) := (BitVec.addInt sum prod)
                            (pure ((prod, sum))))
                        else (pure ((prod, sum)))
                    (pure loop_vars_2)) ) : SailM (Int × (BitVec esize)) )
                let w__7 ← (( do
                  (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth sum)) ) :
                  SailM (BitVec dim_dim_esize) )
                let result := (w__7 : (BitVec dim_dim_esize))
                (pure ((prod, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, k_is_unsigned
  : Bool, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_UMOPA_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7552)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7553) ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := (prod, result)
      for row in [loop_row_lower:loop_row_upper:1]i do
        let (prod, result) := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := (prod, result)
            for col in [loop_col_lower:loop_col_upper:1]i do
              let (prod, result) := loop_vars_1
              loop_vars_1 ← do
                let sum ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let (prod, sum) ← (( do
                  let loop_k_lower : Nat := 0
                  let loop_k_upper : Nat := 1
                  (do
                    let mut loop_vars_2 := (prod, sum)
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let (prod, sum) := loop_vars_2
                      loop_vars_2 ← do
                        let w__2 ← (( do
                          if ((← do
                               (ActivePredicateElement mask1 ((2 *i row) +i k) (Int.ediv esize 2))) : Bool)
                          then
                            (do
                              (ActivePredicateElement mask2 ((2 *i col) +i k) (Int.ediv esize 2)))
                          else (pure false) ) : SailM Bool )
                        if (w__2 : Bool)
                        then
                          (do
                            let w__3 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i row) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                              (BitVec (esize / 2)) )
                            let w__4 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
                            let w__5 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i col) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                              (BitVec (esize / 2)) )
                            let w__6 ← (( do (asl_Int w__5 is_unsigned) ) : SailM Int )
                            let prod : Int := ((w__4 *i w__6) : Int)
                            let prod : Int :=
                              if (sub_op : Bool)
                              then (Neg.neg prod)
                              else prod
                            let sum : (BitVec esize) := (BitVec.addInt sum prod)
                            (pure ((prod, sum))))
                        else (pure ((prod, sum)))
                    (pure loop_vars_2)) ) : SailM (Int × (BitVec esize)) )
                let w__7 ← (( do
                  (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth sum)) ) :
                  SailM (BitVec dim_dim_esize) )
                let result := (w__7 : (BitVec dim_dim_esize))
                (pure ((prod, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, k_is_unsigned
  : Bool, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SMOPS_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7554)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7555) ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := (prod, result)
      for row in [loop_row_lower:loop_row_upper:1]i do
        let (prod, result) := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := (prod, result)
            for col in [loop_col_lower:loop_col_upper:1]i do
              let (prod, result) := loop_vars_1
              loop_vars_1 ← do
                let sum ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let (prod, sum) ← (( do
                  let loop_k_lower : Nat := 0
                  let loop_k_upper : Nat := 1
                  (do
                    let mut loop_vars_2 := (prod, sum)
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let (prod, sum) := loop_vars_2
                      loop_vars_2 ← do
                        let w__2 ← (( do
                          if ((← do
                               (ActivePredicateElement mask1 ((2 *i row) +i k) (Int.ediv esize 2))) : Bool)
                          then
                            (do
                              (ActivePredicateElement mask2 ((2 *i col) +i k) (Int.ediv esize 2)))
                          else (pure false) ) : SailM Bool )
                        if (w__2 : Bool)
                        then
                          (do
                            let w__3 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i row) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                              (BitVec (esize / 2)) )
                            let w__4 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
                            let w__5 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i col) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                              (BitVec (esize / 2)) )
                            let w__6 ← (( do (asl_Int w__5 is_unsigned) ) : SailM Int )
                            let prod : Int := ((w__4 *i w__6) : Int)
                            let prod : Int :=
                              if (sub_op : Bool)
                              then (Neg.neg prod)
                              else prod
                            let sum : (BitVec esize) := (BitVec.addInt sum prod)
                            (pure ((prod, sum))))
                        else (pure ((prod, sum)))
                    (pure loop_vars_2)) ) : SailM (Int × (BitVec esize)) )
                let w__7 ← (( do
                  (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth sum)) ) :
                  SailM (BitVec dim_dim_esize) )
                let result := (w__7 : (BitVec dim_dim_esize))
                (pure ((prod, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, k_is_unsigned
  : Bool, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_UMOPS_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7556)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7557) ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := (prod, result)
      for row in [loop_row_lower:loop_row_upper:1]i do
        let (prod, result) := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := (prod, result)
            for col in [loop_col_lower:loop_col_upper:1]i do
              let (prod, result) := loop_vars_1
              loop_vars_1 ← do
                let sum ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let (prod, sum) ← (( do
                  let loop_k_lower : Nat := 0
                  let loop_k_upper : Nat := 1
                  (do
                    let mut loop_vars_2 := (prod, sum)
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let (prod, sum) := loop_vars_2
                      loop_vars_2 ← do
                        let w__2 ← (( do
                          if ((← do
                               (ActivePredicateElement mask1 ((2 *i row) +i k) (Int.ediv esize 2))) : Bool)
                          then
                            (do
                              (ActivePredicateElement mask2 ((2 *i col) +i k) (Int.ediv esize 2)))
                          else (pure false) ) : SailM Bool )
                        if (w__2 : Bool)
                        then
                          (do
                            let w__3 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i row) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                              (BitVec (esize / 2)) )
                            let w__4 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
                            let w__5 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i col) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                              (BitVec (esize / 2)) )
                            let w__6 ← (( do (asl_Int w__5 is_unsigned) ) : SailM Int )
                            let prod : Int := ((w__4 *i w__6) : Int)
                            let prod : Int :=
                              if (sub_op : Bool)
                              then (Neg.neg prod)
                              else prod
                            let sum : (BitVec esize) := (BitVec.addInt sum prod)
                            (pure ((prod, sum))))
                        else (pure ((prod, sum)))
                    (pure loop_vars_2)) ) : SailM (Int × (BitVec esize)) )
                let w__7 ← (( do
                  (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth sum)) ) :
                  SailM (BitVec dim_dim_esize) )
                let result := (w__7 : (BitVec dim_dim_esize))
                (pure ((prod, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


def decode_LUTI2_Z_ZTZ__ (i4 : (BitVec 4)) (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let isize : Nat := 2
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let imm : Int := (BitVec.toNat i4)
  let nreg : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_LUTI2_Z_ZTZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) isize (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_LUTI2_Z_ZTZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) isize (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_LUTI2_Z_ZTZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) isize (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_LUTI2_Z_ZTZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) isize (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_LUTI2_Z_ZTZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) isize (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_LUTI4_Z_ZTZ__ (i3 : (BitVec 3)) (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let isize : Nat := 4
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let imm : Int := (BitVec.toNat i3)
  let nreg : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_LUTI4_Z_ZTZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) isize (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_LUTI4_Z_ZTZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) isize (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_LUTI4_Z_ZTZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) isize (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_LUTI4_Z_ZTZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) isize (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_LUTI4_Z_ZTZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (imm)) isize (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_LUTI2_MZ2_ZTZ_1 (i3 : (BitVec 3)) (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let isize : Nat := 2
  let n : Int := (BitVec.toNat Zn)
  let dstride : Nat := 1
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let imm : Int := (BitVec.toNat i3)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_LUTI2_MZ2_ZTZ_1 128 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_LUTI2_MZ2_ZTZ_1 256 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_LUTI2_MZ2_ZTZ_1 512 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_LUTI2_MZ2_ZTZ_1 1024 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_LUTI2_MZ2_ZTZ_1 2048 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


end ArmFull.Functions
