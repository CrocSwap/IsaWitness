import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0063
import ArmFull.Fn.M0087
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0152
import ArmFull.Fn.M0202
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925
import ArmFull.Fn.M0928

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

def decode_aarch32_instrs_MCRR_A1enc_A_txt (cond : (BitVec 4)) (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:7125.29-7125.30"
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let cp : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access coproc 0)])) == 0#1) : Bool)
        then 14
        else 15
      if (((t == 15) || (t2 == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MCRR_Op_A_txt (Sail.Int.toNatChecked (cp)) (Sail.Int.toNatChecked (t))
        (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_MCRR_T1enc_A_txt (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let cp : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access coproc 0)])) == 0#1) : Bool)
        then 14
        else 15
      if (((t == 15) || (t2 == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MCRR_Op_A_txt (Sail.Int.toNatChecked (cp)) (Sail.Int.toNatChecked (t))
        (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_MRRC_A1enc_A_txt (cond : (BitVec 4)) (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:7844.29-7844.30"
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let cp : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access coproc 0)])) == 0#1) : Bool)
        then 14
        else 15
      if ((((t == 15) || (t2 == 15)) || (t == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MRRC_Op_A_txt (Sail.Int.toNatChecked (cp)) (Sail.Int.toNatChecked (t))
        (Sail.Int.toNatChecked (t2))))
  else (pure (()))


def decode_aarch32_instrs_MRRC_T1enc_A_txt (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let cp : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access coproc 0)])) == 0#1) : Bool)
        then 14
        else 15
      if ((((t == 15) || (t2 == 15)) || (t == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MRRC_Op_A_txt (Sail.Int.toNatChecked (cp)) (Sail.Int.toNatChecked (t))
        (Sail.Int.toNatChecked (t2))))
  else (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_long_destination
  : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VABA_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let absdiff ← (( do (undefined_int_at (← occLabel 3334) ()) ) : SailM Int )
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3335)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3336)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (absdiff, op1, op2) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (absdiff, op1, op2)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (absdiff, op1, op2) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (absdiff, op1, op2)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (absdiff, op1, op2) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (Din_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 := (w__1 : (BitVec esize))
                let w__2 ← (( do (Din_read (m +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let op2 := (w__3 : (BitVec esize))
                let w__4 ← (( do (asl_Int op1 is_unsigned) ) : SailM Int )
                let w__5 ← (( do (asl_Int op2 is_unsigned) ) : SailM Int )
                let absdiff : Int := ((Int.natAbs (w__4 -i w__5)) : Int)
                if (long_destination : Bool)
                then
                  (do
                    let w__6 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                    let w__7 ← (( do (Qin_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                    let w__8 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read w__7 e
                        (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                    let w__9 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e
                        (Sail.Int.toNatChecked ((2 *i esize)))
                        (Sail.BitVec.castWidth (BitVec.addInt w__8 absdiff)))) ) : SailM
                      (BitVec 128) )
                    (Q_set (Int.shiftr d 1) w__9))
                else
                  (do
                    let w__10 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__11 ← (( do (Din_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__12 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__11 e esize)) ) :
                      SailM (BitVec esize) )
                    let w__13 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__10 e esize
                        (Sail.BitVec.castWidth (BitVec.addInt w__12 absdiff)))) ) : SailM
                      (BitVec 64) )
                    (D_set (d +i r) w__13))
                (pure ((absdiff, op1, op2)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_long_destination
  : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VABD_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let absdiff ← (( do (undefined_int_at (← occLabel 3339) ()) ) : SailM Int )
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3340)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3341)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let (absdiff, op1, op2) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (absdiff, op1, op2)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (absdiff, op1, op2) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (absdiff, op1, op2)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (absdiff, op1, op2) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (Din_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 := (w__1 : (BitVec esize))
                let w__2 ← (( do (Din_read (m +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let op2 := (w__3 : (BitVec esize))
                let w__4 ← (( do (asl_Int op1 is_unsigned) ) : SailM Int )
                let w__5 ← (( do (asl_Int op2 is_unsigned) ) : SailM Int )
                let absdiff : Int := ((Int.natAbs (w__4 -i w__5)) : Int)
                if (long_destination : Bool)
                then
                  (do
                    let w__6 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                    let w__7 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e
                        (Sail.Int.toNatChecked ((2 *i esize)))
                        (Sail.BitVec.castWidth (integer_subrange absdiff ((2 *i esize) -i 1) 0)))) )
                      : SailM (BitVec 128) )
                    (Q_set (Int.shiftr d 1) w__7))
                else
                  (do
                    let w__8 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__9 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__8 e esize
                        (Sail.BitVec.castWidth (integer_subrange absdiff (esize -i 1) 0)))) ) :
                      SailM (BitVec 64) )
                    (D_set (d +i r) w__9))
                (pure ((absdiff, op1, op2)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VADDHN_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3366)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Qin_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e (Sail.Int.toNatChecked ((2 *i esize)))))
            ) : SailM (BitVec (2 * esize)) )
          let w__2 ← (( do (Qin_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e (Sail.Int.toNatChecked ((2 *i esize)))))
            ) : SailM (BitVec (2 * esize)) )
          let result := ((w__1 + w__3) : (BitVec (2 * esize)))
          let w__4 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result
                (Sail.Int.toNatChecked (((2 *i esize) -i 1))) esize)))) ) : SailM (BitVec 64) )
          (D_set d w__5)
          (pure (result))
      (pure loop_vars)) ) : SailM (BitVec (2 * esize)) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VADD_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__1 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
              let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) : SailM
                (BitVec esize) )
              let w__3 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
              let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                (BitVec esize) )
              let w__5 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
                  (Sail.BitVec.castWidth (w__2 + w__4)))) ) : SailM (BitVec 64) )
              (D_set (d +i r) w__5)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_is_vaddw :
  Bool, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VADDL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (is_vaddw : Bool) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3367) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let op1 ← (( do (undefined_int_at (← occLabel 3368) ()) ) : SailM Int )
          let op1 ← (( do
            if (is_vaddw : Bool)
            then
              (do
                let w__0 ← (( do (Qin_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
                let w__1 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                (asl_Int w__1 is_unsigned))
            else
              (do
                let w__3 ← (( do (Din_read n) ) : SailM (BitVec 64) )
                let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                  (BitVec esize) )
                (asl_Int w__4 is_unsigned)) ) : SailM Int )
          let op1 : Int := op1
          let w__6 ← (( do (Din_read m) ) : SailM (BitVec 64) )
          let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__6 e esize)) ) : SailM
            (BitVec esize) )
          let w__8 ← (( do (asl_Int w__7 is_unsigned) ) : SailM Int )
          let result : Int := ((op1 +i w__8) : Int)
          let w__9 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
          let w__10 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__9 e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth (integer_subrange result ((2 *i esize) -i 1) 0)))) ) : SailM
            (BitVec 128) )
          (Q_set (Int.shiftr d 1) w__10)
          (pure (result))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VAND_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
        let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
        (D_set (d +i r) (w__0 &&& w__1))
    (pure loop_vars))


/-- Type quantifiers: d : Nat, regs : Nat, List.elem regs [1, 2] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VBIC_i_Op_A_txt (d : Nat) (imm64 : (BitVec 64)) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
        (D_set (d +i r) (w__0 &&& (Complement.complement imm64)))
    (pure loop_vars))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VBIC_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
        let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
        (D_set (d +i r) (w__0 &&& (Complement.complement w__1)))
    (pure loop_vars))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VBIF_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (operation : VBitOps) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        match operation with
        | .VBitOps_VBIF =>
          (do
            let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
            let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
            let w__2 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
            let w__3 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
            (D_set (d +i r) ((w__0 &&& w__1) ||| (w__2 &&& (Complement.complement w__3)))))
        | .VBitOps_VBIT =>
          (do
            let w__4 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
            let w__5 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
            let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
            let w__7 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
            (D_set (d +i r) ((w__4 &&& w__5) ||| (w__6 &&& (Complement.complement w__7)))))
        | .VBitOps_VBSL =>
          (do
            let w__8 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
            let w__9 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
            let w__10 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
            let w__11 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
            (D_set (d +i r) ((w__8 &&& w__9) ||| (w__10 &&& (Complement.complement w__11)))))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, regs : Nat, List.elem regs
  [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCLS_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
              let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) : SailM
                (BitVec esize) )
              let w__3 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
                  (Sail.BitVec.castWidth (integer_subrange (CountLeadingSignBits w__2) (esize -i 1)
                    0)))) ) : SailM (BitVec 64) )
              (D_set (d +i r) w__3)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, regs : Nat, List.elem regs
  [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCLZ_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
              let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) : SailM
                (BitVec esize) )
              let w__3 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
                  (Sail.BitVec.castWidth (integer_subrange (CountLeadingZeroBits w__2) (esize -i 1)
                    0)))) ) : SailM (BitVec 64) )
              (D_set (d +i r) w__3)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, m : Nat, regs : Nat, List.elem regs
  [1, 2] ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 8 ∧ elements = 8 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCNT_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
              let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) : SailM
                (BitVec esize) )
              let w__3 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
                  (Sail.BitVec.castWidth (integer_subrange (BitCount w__2) (esize -i 1) 0)))) ) :
                SailM (BitVec 64) )
              (D_set (d +i r) w__3)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, regs : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 15 ∧
  List.elem regs [1, 2] ∧
  List.elem esize [8, 16, 32] ∧ List.elem elements [2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VDUP_r_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (regs : Nat) (t : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let w__0 ← (( do (R_read t) ) : SailM (BitVec 32) )
  let scalar : (BitVec (0 + (esize - 1 - 0 + 1))) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0 (Sail.Int.toNatChecked ((esize -i 1))) 0))
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__1 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__2 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__1 e esize (Sail.BitVec.castWidth scalar)))
                ) : SailM (BitVec 64) )
              (D_set (d +i r) w__2)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, index : Nat, m : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32] ∧ List.elem elements [2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VDUP_s_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (index : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let w__0 ← (( do (D_read m) ) : SailM (BitVec 64) )
  let scalar ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index esize)) ) : SailM
    (BitVec esize) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__1 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__2 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__1 e esize (Sail.BitVec.castWidth scalar)))
                ) : SailM (BitVec 64) )
              (D_set (d +i r) w__2)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VEOR_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
        let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
        (D_set (d +i r) (w__0 ^^^ w__1))
    (pure loop_vars))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, position : Nat, k_quadword_operation : Bool, 0 ≤
  position ∧
  position ≤ 120 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VEXT_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (position : Nat) (quadword_operation : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  if (quadword_operation : Bool)
  then
    (do
      let w__0 ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
      let w__1 ← (( do (Q_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
      (Q_set (Int.shiftl d 1)
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb (w__0 +++ w__1)
          (Sail.Int.toNatChecked ((position +i 127))) position))))
  else
    (do
      ArmFull.assert ((0 ≤b position) && ((position ≤b (position +i 63)) && ((position +i 63) <b 128))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:23935.96-23935.97"
      let w__2 ← (( do (D_read m) ) : SailM (BitVec 64) )
      let w__3 ← (( do (D_read n) ) : SailM (BitVec 64) )
      (D_set d
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb (w__2 +++ w__3)
          (Sail.Int.toNatChecked ((position +i 63))) position))))


end ArmFull.Functions
