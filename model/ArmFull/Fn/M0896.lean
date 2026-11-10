import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0218
import ArmFull.Fn.M0227
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
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6999)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7000) ()) ) : SailM Int )
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
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SUMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7001)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7002) ()) ) : SailM Int )
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
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_USMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7003)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7004) ()) ) : SailM Int )
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
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_UMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7005)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7006) ()) ) : SailM Int )
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
def execute_SMOPA_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7007)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7008) ()) ) : SailM Int )
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
def execute_SUMOPA_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7009)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7010) ()) ) : SailM Int )
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
def execute_USMOPA_ZA_PP_ZZ_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (sub_op : Bool) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7011)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7012) ()) ) : SailM Int )
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


end ArmFull.Functions
