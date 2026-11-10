import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0147
import ArmFull.Fn.M0178
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840
import ArmFull.Fn.M1040
import ArmFull.Fn.M1042
import ArmFull.Fn.M1044

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
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMGT_P_P_Z0__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
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
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5043)
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
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) :
                SailM (BitVec esize) )
              let res ← (( do (undefined_bool_at (← occLabel 5044) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_EQ =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:738.59-738.60"
                    let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareEQ element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__3))
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:742.59-742.60"
                    let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__5))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:746.59-746.60"
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__7))
                | .Cmp_NE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:750.59-750.60"
                    let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareNE element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__9))
                | .Cmp_LT =>
                  (do
                    ArmFull.assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:754.117-754.118"
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0)) element
                      w__11))
                | .Cmp_LE =>
                  (do
                    ArmFull.assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:758.117-758.118"
                    let w__13 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0)) element
                      w__13))
                | _ => (pure (res)) ) : SailM Bool )
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMLT_P_P_Z0__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
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
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5045)
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
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) :
                SailM (BitVec esize) )
              let res ← (( do (undefined_bool_at (← occLabel 5046) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_EQ =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:841.59-841.60"
                    let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareEQ element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__3))
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:845.59-845.60"
                    let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__5))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:849.59-849.60"
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__7))
                | .Cmp_NE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:853.59-853.60"
                    let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareNE element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__9))
                | .Cmp_LT =>
                  (do
                    ArmFull.assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:857.117-857.118"
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0)) element
                      w__11))
                | .Cmp_LE =>
                  (do
                    ArmFull.assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:861.117-861.118"
                    let w__13 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0)) element
                      w__13))
                | _ => (pure (res)) ) : SailM Bool )
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMLE_P_P_Z0__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
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
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5047)
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
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) :
                SailM (BitVec esize) )
              let res ← (( do (undefined_bool_at (← occLabel 5048) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_EQ =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:944.59-944.60"
                    let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareEQ element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__3))
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:948.59-948.60"
                    let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__5))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:952.59-952.60"
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__7))
                | .Cmp_NE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:956.59-956.60"
                    let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareNE element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__9))
                | .Cmp_LT =>
                  (do
                    ArmFull.assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:960.117-960.118"
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0)) element
                      w__11))
                | .Cmp_LE =>
                  (do
                    ArmFull.assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:964.117-964.118"
                    let w__13 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0)) element
                      w__13))
                | _ => (pure (res)) ) : SailM Bool )
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMEQ_P_P_Z0__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
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
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5049)
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
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) :
                SailM (BitVec esize) )
              let res ← (( do (undefined_bool_at (← occLabel 5050) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_EQ =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:1047.59-1047.60"
                    let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareEQ element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__3))
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:1051.59-1051.60"
                    let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__5))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:1055.59-1055.60"
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__7))
                | .Cmp_NE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:1059.59-1059.60"
                    let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareNE element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__9))
                | .Cmp_LT =>
                  (do
                    ArmFull.assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:1063.117-1063.118"
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0)) element
                      w__11))
                | .Cmp_LE =>
                  (do
                    ArmFull.assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:1067.117-1067.118"
                    let w__13 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0)) element
                      w__13))
                | _ => (pure (res)) ) : SailM Bool )
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMNE_P_P_Z0__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
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
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5051)
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
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) :
                SailM (BitVec esize) )
              let res ← (( do (undefined_bool_at (← occLabel 5052) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_EQ =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:1150.59-1150.60"
                    let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareEQ element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__3))
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:1154.59-1154.60"
                    let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__5))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:1158.59-1158.60"
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__7))
                | .Cmp_NE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:1162.59-1162.60"
                    let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareNE element (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0))
                      w__9))
                | .Cmp_LT =>
                  (do
                    ArmFull.assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:1166.117-1166.118"
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0)) element
                      w__11))
                | .Cmp_LE =>
                  (do
                    ArmFull.assert (((((esize -i 1) -i 0) +i 1) == 16) || (((((esize -i 1) -i 0) +i 1) == 32) || ((((esize -i 1) -i 0) +i 1) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:1170.117-1170.118"
                    let w__13 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE (Sail.BitVec.castWidth (integer_subrange 0 (esize -i 1) 0)) element
                      w__13))
                | _ => (pure (res)) ) : SailM Bool )
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n
  : Nat, s_esize : Nat, s_esize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_Z_P_Z_D2X (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let res ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPToFixed
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) 0
                  is_unsigned w__3 rounding d_esize)) ) : SailM (BitVec d_esize) )
              let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend res esize is_unsigned)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__4)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n
  : Nat, s_esize : Nat, s_esize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_Z_P_Z_D2W (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let res ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPToFixed
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) 0
                  is_unsigned w__3 rounding d_esize)) ) : SailM (BitVec d_esize) )
              let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend res esize is_unsigned)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__4)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n
  : Nat, s_esize : Nat, s_esize = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 32 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_Z_P_Z_S2W (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let res ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPToFixed
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) 0
                  is_unsigned w__3 rounding d_esize)) ) : SailM (BitVec d_esize) )
              let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend res esize is_unsigned)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__4)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n
  : Nat, s_esize : Nat, s_esize = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTZU_Z_P_Z_S2X (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let res ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPToFixed
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) 0
                  is_unsigned w__3 rounding d_esize)) ) : SailM (BitVec d_esize) )
              let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend res esize is_unsigned)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__4)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
