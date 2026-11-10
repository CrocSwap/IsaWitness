import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0146
import ArmFull.Fn.M0218
import ArmFull.Fn.M0227
import ArmFull.Fn.M0238
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

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 64 ∧
  List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_UMOPA_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7013)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7014) ()) ) : SailM Int )
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
                  let loop_k_upper : Nat := 3
                  (do
                    let mut loop_vars_2 := (prod, sum)
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let (prod, sum) := loop_vars_2
                      loop_vars_2 ← do
                        let w__2 ← (( do
                          if ((← do
                               (ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4))) : Bool)
                          then
                            (do
                              (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4)))
                          else (pure false) ) : SailM Bool )
                        if (w__2 : Bool)
                        then
                          (do
                            let w__3 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i row) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                              (BitVec (esize / 4)) )
                            let w__4 ← (( do (asl_Int w__3 op1_unsigned) ) : SailM Int )
                            let w__5 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i col) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                              (BitVec (esize / 4)) )
                            let w__6 ← (( do (asl_Int w__5 op2_unsigned) ) : SailM Int )
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


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 64 ∧
  List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SMOPS_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7015)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7016) ()) ) : SailM Int )
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
                  let loop_k_upper : Nat := 3
                  (do
                    let mut loop_vars_2 := (prod, sum)
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let (prod, sum) := loop_vars_2
                      loop_vars_2 ← do
                        let w__2 ← (( do
                          if ((← do
                               (ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4))) : Bool)
                          then
                            (do
                              (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4)))
                          else (pure false) ) : SailM Bool )
                        if (w__2 : Bool)
                        then
                          (do
                            let w__3 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i row) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                              (BitVec (esize / 4)) )
                            let w__4 ← (( do (asl_Int w__3 op1_unsigned) ) : SailM Int )
                            let w__5 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i col) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                              (BitVec (esize / 4)) )
                            let w__6 ← (( do (asl_Int w__5 op2_unsigned) ) : SailM Int )
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


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 64 ∧
  List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SUMOPS_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7017)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7018) ()) ) : SailM Int )
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
                  let loop_k_upper : Nat := 3
                  (do
                    let mut loop_vars_2 := (prod, sum)
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let (prod, sum) := loop_vars_2
                      loop_vars_2 ← do
                        let w__2 ← (( do
                          if ((← do
                               (ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4))) : Bool)
                          then
                            (do
                              (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4)))
                          else (pure false) ) : SailM Bool )
                        if (w__2 : Bool)
                        then
                          (do
                            let w__3 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i row) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                              (BitVec (esize / 4)) )
                            let w__4 ← (( do (asl_Int w__3 op1_unsigned) ) : SailM Int )
                            let w__5 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i col) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                              (BitVec (esize / 4)) )
                            let w__6 ← (( do (asl_Int w__5 op2_unsigned) ) : SailM Int )
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


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 64 ∧
  List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_USMOPS_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7019)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7020) ()) ) : SailM Int )
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
                  let loop_k_upper : Nat := 3
                  (do
                    let mut loop_vars_2 := (prod, sum)
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let (prod, sum) := loop_vars_2
                      loop_vars_2 ← do
                        let w__2 ← (( do
                          if ((← do
                               (ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4))) : Bool)
                          then
                            (do
                              (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4)))
                          else (pure false) ) : SailM Bool )
                        if (w__2 : Bool)
                        then
                          (do
                            let w__3 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i row) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                              (BitVec (esize / 4)) )
                            let w__4 ← (( do (asl_Int w__3 op1_unsigned) ) : SailM Int )
                            let w__5 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i col) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                              (BitVec (esize / 4)) )
                            let w__6 ← (( do (asl_Int w__5 op2_unsigned) ) : SailM Int )
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


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 64 ∧
  List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_UMOPS_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7021)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7022) ()) ) : SailM Int )
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
                  let loop_k_upper : Nat := 3
                  (do
                    let mut loop_vars_2 := (prod, sum)
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let (prod, sum) := loop_vars_2
                      loop_vars_2 ← do
                        let w__2 ← (( do
                          if ((← do
                               (ActivePredicateElement mask1 ((4 *i row) +i k) (Int.ediv esize 4))) : Bool)
                          then
                            (do
                              (ActivePredicateElement mask2 ((4 *i col) +i k) (Int.ediv esize 4)))
                          else (pure false) ) : SailM Bool )
                        if (w__2 : Bool)
                        then
                          (do
                            let w__3 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i row) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                              (BitVec (esize / 4)) )
                            let w__4 ← (( do (asl_Int w__3 op1_unsigned) ) : SailM Int )
                            let w__5 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i col) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                              (BitVec (esize / 4)) )
                            let w__6 ← (( do (asl_Int w__5 op2_unsigned) ) : SailM Int )
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


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 15 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ d = 0 ∧ (is_VL VL) -/
def execute_MOVA_ZA_P_RZ_B (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read d esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              (Elem_set result e esize (Sail.BitVec.castWidth element)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (ZAslice_set d esize vertical slice_name VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ List.elem d [0, 1] ∧ (is_VL VL) -/
def execute_MOVA_ZA_P_RZ_H (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read d esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              (Elem_set result e esize (Sail.BitVec.castWidth element)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (ZAslice_set d esize vertical slice_name VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1, 2, 3] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ List.elem d [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_MOVA_ZA_P_RZ_W (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read d esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              (Elem_set result e esize (Sail.BitVec.castWidth element)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (ZAslice_set d esize vertical slice_name VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_MOVA_ZA_P_RZ_D (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read d esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              (Elem_set result e esize (Sail.BitVec.castWidth element)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (ZAslice_set d esize vertical slice_name VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
