import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0195
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0227
import ArmFull.Fn.M0238
import ArmFull.Fn.M0840
import ArmFull.Fn.M0843

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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  offset = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_MOVA_ZA_P_RZ_Q (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
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
  0 ≤ offset ∧
  offset ≤ 15 ∧
  n = 0 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_Z_P_RZA_B (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
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
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem n [0, 1] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_Z_P_RZA_H (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
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
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1, 2, 3] ∧
  List.elem n [0, 1, 2, 3] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_Z_P_RZA_W (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
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
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1] ∧
  List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_Z_P_RZA_D (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
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
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  offset = 0 ∧
  0 ≤ n ∧
  n ≤ 15 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVA_Z_P_RZA_Q (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
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
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_ADDHA_ZA_PP_Z_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand_src ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand_acc ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) )
    : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7051)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_col_lower : Nat := 0
    let loop_col_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for col in [loop_col_lower:loop_col_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand_src col esize)) ) :
            SailM (BitVec esize) )
          let loop_row_lower : Nat := 0
          let loop_row_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for row in [loop_row_lower:loop_row_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let res ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand_acc ((row *i dim) +i col) esize))
                  ) : SailM (BitVec esize) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row esize)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col esize))
                  else (pure false) ) : SailM Bool )
                let res : (BitVec esize) :=
                  if (w__2 : Bool)
                  then (res + element)
                  else res
                (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth res))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  esize = 64 ∧
  List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_ADDHA_ZA_PP_Z_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand_src ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand_acc ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) )
    : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7052)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_col_lower : Nat := 0
    let loop_col_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for col in [loop_col_lower:loop_col_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand_src col esize)) ) :
            SailM (BitVec esize) )
          let loop_row_lower : Nat := 0
          let loop_row_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for row in [loop_row_lower:loop_row_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let res ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand_acc ((row *i dim) +i col) esize))
                  ) : SailM (BitVec esize) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row esize)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col esize))
                  else (pure false) ) : SailM Bool )
                let res : (BitVec esize) :=
                  if (w__2 : Bool)
                  then (res + element)
                  else res
                (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth res))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_ADDVA_ZA_PP_Z_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand_src ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand_acc ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) )
    : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7053)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand_src row esize)) ) :
            SailM (BitVec esize) )
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let res ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand_acc ((row *i dim) +i col) esize))
                  ) : SailM (BitVec esize) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row esize)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col esize))
                  else (pure false) ) : SailM Bool )
                let res : (BitVec esize) :=
                  if (w__2 : Bool)
                  then (res + element)
                  else res
                (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth res))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  esize = 64 ∧
  List.elem da [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_ADDVA_ZA_PP_Z_64 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand_src ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand_acc ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) )
    : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7054)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand_src row esize)) ) :
            SailM (BitVec esize) )
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let res ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand_acc ((row *i dim) +i col) esize))
                  ) : SailM (BitVec esize) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row esize)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col esize))
                  else (pure false) ) : SailM Bool )
                let res : (BitVec esize) :=
                  if (w__2 : Bool)
                  then (res + element)
                  else res
                (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth res))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


def decode_ZERO_ZA_I__ (imm8 : (BitVec 8)) : SailM Unit := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let mask : (BitVec 8) := imm8
  let esize : Nat := 64
  match SVL with
  | 128 =>
    (do
      (execute_ZERO_ZA_I__ 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize))) esize
        mask))
  | 256 =>
    (do
      (execute_ZERO_ZA_I__ 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize))) esize
        mask))
  | 512 =>
    (do
      (execute_ZERO_ZA_I__ 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize))) esize
        mask))
  | 1024 =>
    (do
      (execute_ZERO_ZA_I__ 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize))) esize
        mask))
  | 2048 =>
    (do
      (execute_ZERO_ZA_I__ 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize))) esize
        mask))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 15 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 8 ∧ d = 0 ∧ (is_VL VL) -/
def execute_MOVA_ZA2_Z_B1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
          (BitVec VL) )
        (ZAslice_set d esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ List.elem d [0, 1] ∧ (is_VL VL) -/
def execute_MOVA_ZA2_Z_H1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
          (BitVec VL) )
        (ZAslice_set d esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1, 2, 3] ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 32 ∧ List.elem d [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_MOVA_ZA2_Z_W1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
          (BitVec VL) )
        (ZAslice_set d esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  offset = 0 ∧
  nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ esize = 64 ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_MOVA_ZA2_Z_D1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
          (BitVec VL) )
        (ZAslice_set d esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 15 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 8 ∧ d = 0 ∧ (is_VL VL) -/
def execute_MOVA_ZA4_Z_B1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
          (BitVec VL) )
        (ZAslice_set d esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


end ArmFull.Functions
