import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0041
import ArmFull.Fn.M0044
import ArmFull.Fn.M0049
import ArmFull.Fn.M0054
import ArmFull.Fn.M0059
import ArmFull.Fn.M0087
import ArmFull.Fn.M0124
import ArmFull.Fn.M0145
import ArmFull.Fn.M0175
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0227
import ArmFull.Fn.M0254
import ArmFull.Fn.M0260
import ArmFull.Fn.M0852
import ArmFull.Fn.M0853
import ArmFull.Fn.M0854

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

/-- Type quantifiers: t : Int -/
def ATS1CUR_SysRegWrite32_592c369d819e223e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__4) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__11 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_AT w__11 TranslationStage_1 EL0 ATAccess_Read))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_AT w__12 TranslationStage_1 EL0 ATAccess_Read))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_AT w__13 TranslationStage_1 EL0 ATAccess_Read))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ATS1CUW_SysRegWrite32_eb4fd0807cfcfcfb (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__4) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__11 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_AT w__11 TranslationStage_1 EL0 ATAccess_Write))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_AT w__12 TranslationStage_1 EL0 ATAccess_Write))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_AT w__13 TranslationStage_1 EL0 ATAccess_Write))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ATS1HR_SysRegWrite32_dc67c53b4eef830a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__4) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__11 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_AT w__11 TranslationStage_1 EL2 ATAccess_Read))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__12 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_AT w__12 TranslationStage_1 EL2 ATAccess_Read))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ATS1HW_SysRegWrite32_6bb51bbf34dda57b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__4) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__11 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_AT w__11 TranslationStage_1 EL2 ATAccess_Write))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__12 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_AT w__12 TranslationStage_1 EL2 ATAccess_Write))
              else (pure (())))))


def decode_aarch32_instrs_BKPT_A1enc_A_txt (cond : (BitVec 4)) (imm12 : (BitVec 12)) (imm4 : (BitVec 4)) : SailM Unit := do
  ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:1917.25-1917.26"
  let imm16 : (BitVec 16) := (imm12 +++ imm4)
  if ((cond != 0b1110#4) : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  (execute_aarch32_instrs_BKPT_Op_A_txt imm16)


def decode_aarch32_instrs_BKPT_T1enc_A_txt (imm8 : (BitVec 8)) : SailM Unit := do
  let imm16 : (BitVec 16) := (Sail.BitVec.zeroExtend imm8 16)
  (execute_aarch32_instrs_BKPT_Op_A_txt imm16)


/-- Type quantifiers: cp : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧
  t2 ≤ 15 ∧ 0 ≤ t ∧ t ≤ 15 ∧ List.elem cp [14, 15] -/
def execute_aarch32_instrs_MCRR_Op_A_txt (cp : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  let w__0 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
  (AArch32_SysRegWrite64 cp w__0 t t2)


/-- Type quantifiers: cp : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧
  t2 ≤ 15 ∧ 0 ≤ t ∧ t ≤ 15 ∧ List.elem cp [14, 15] -/
def execute_aarch32_instrs_MRRC_Op_A_txt (cp : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  let w__0 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
  (AArch32_SysRegRead64 cp w__0 t t2)


def decode_aarch32_instrs_ESB_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:45997.29-45997.30"
      let w__1 ← (( do (HaveRASExt ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          (EndOfInstruction ()))
      else (pure (()))
      if ((cond != 0b1110#4) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ESB_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_ESB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveRASExt ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          (EndOfInstruction ()))
      else (pure (()))
      let w__2 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ESB_Op_A_txt ()))
  else (pure (()))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, k_neg : Bool, 0
  ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (neg : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3911)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int_at (← occLabel 3912) ()) ) : SailM Int )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element : Int := ((BitVec.toInt w__0) : Int)
          let element : Int :=
            if (neg : Bool)
            then (Neg.neg element)
            else (Int.natAbs element)
          let w__1 ← (( do
            (Elem_set result e esize
              (Sail.BitVec.castWidth (integer_subrange element (esize -i 1) 0))) ) : SailM
            (BitVec datasize) )
          let result := (w__1 : (BitVec datasize))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_sub_op
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3915)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3916)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3917)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__0 : (BitVec esize))
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 := (w__1 : (BitVec esize))
          let result ← (( do
            if (sub_op : Bool)
            then
              (do
                (Elem_set result e esize (Sail.BitVec.castWidth (element1 - element2))))
            else
              (do
                (Elem_set result e esize (Sail.BitVec.castWidth (element1 + element2)))) ) : SailM
            (BitVec datasize) )
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, part :
  Nat, k_round : Bool, k_sub_op : Bool, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (round : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read m (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3933)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int_at (← occLabel 3934) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 3935) ()) ) : SailM Int )
  let sum ← (( do (undefined_int_at (← occLabel 3936) ()) ) : SailM Int )
  let (element1, element2, result, sum) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result, sum)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result, sum) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
          let element1 : Int := ((BitVec.toNat w__0) : Int)
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
          let element2 : Int := ((BitVec.toNat w__1) : Int)
          let sum : Int :=
            if (sub_op : Bool)
            then (element1 -i element2)
            else (element1 +i element2)
          let w__2 ← (( do (RShr sum esize round) ) : SailM Int )
          let sum : Int := (w__2 : Int)
          let w__3 ← (( do
            (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange sum (esize -i 1) 0)))
            ) : SailM (BitVec datasize) )
          let result := (w__3 : (BitVec datasize))
          (pure ((element1, element2, result, sum)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec datasize) × Int) )
  (Vpart_set d part datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3937)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let concat : (BitVec (2 * datasize)) := (Sail.BitVec.castWidth (operand2 +++ operand1))
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3938)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3939)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read concat (2 *i e) esize)) ) :
            SailM (BitVec esize) )
          let element1 := (w__0 : (BitVec esize))
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read concat ((2 *i e) +i 1) esize))
            ) : SailM (BitVec esize) )
          let element2 := (w__1 : (BitVec esize))
          let w__2 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth (element1 + element2)))
            ) : SailM (BitVec datasize) )
          let result := (w__2 : (BitVec datasize))
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


def decode_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HaveAESExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let decrypt : Bool := (D == 1#1)
  (execute_aarch64_instrs_vector_crypto_aes_round (Sail.Int.toNatChecked (d)) decrypt
    (Sail.Int.toNatChecked (n)))


def decode_aese_advsimd_aarch64_instrs_vector_crypto_aes_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HaveAESExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let decrypt : Bool := (D == 1#1)
  (execute_aarch64_instrs_vector_crypto_aes_round (Sail.Int.toNatChecked (d)) decrypt
    (Sail.Int.toNatChecked (n)))


def decode_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HaveAESExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let decrypt : Bool := (D == 1#1)
  (execute_aarch64_instrs_vector_crypto_aes_mix (Sail.Int.toNatChecked (d)) decrypt
    (Sail.Int.toNatChecked (n)))


def decode_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HaveAESExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let decrypt : Bool := (D == 1#1)
  (execute_aarch64_instrs_vector_crypto_aes_mix (Sail.Int.toNatChecked (d)) decrypt
    (Sail.Int.toNatChecked (n)))


/-- Type quantifiers: d : Nat, datasize : Nat, k_invert : Bool, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (d : Nat) (datasize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : LogicalOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3956)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand2 : (BitVec datasize) :=
    if (invert : Bool)
    then (Complement.complement operand2)
    else operand2
  let result : (BitVec datasize) :=
    match op with
    | .LogicalOp_AND => (operand1 &&& operand2)
    | .LogicalOp_ORR => (operand1 ||| operand2)
    | _ => result
  (V_set d datasize (Sail.BitVec.castWidth result))


def decode_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSHA3Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  (execute_aarch64_instrs_vector_crypto_sha3_bcax (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


/-- Type quantifiers: datasize : Nat, rd : Nat, 0 ≤ rd ∧
  rd ≤ 31 ∧ List.elem datasize [64, 128] -/
def execute_aarch64_instrs_vector_logical (datasize : Nat) (imm : (BitVec datasize)) (operation : ImmediateOp) (rd : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3991)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3992)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let result ← (( do
    match operation with
    | .ImmediateOp_MOVI => (pure (imm))
    | .ImmediateOp_MVNI =>
      (let result : (BitVec datasize) := (Complement.complement imm)
      (pure (result)))
    | .ImmediateOp_ORR =>
      (do
        let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read rd datasize)) ) : SailM
          (BitVec datasize) )
        let result : (BitVec datasize) := (operand ||| imm)
        (pure (result)))
    | .ImmediateOp_BIC =>
      (do
        let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read rd datasize)) ) : SailM
          (BitVec datasize) )
        let result : (BitVec datasize) := (operand &&& (Complement.complement imm))
        (pure (result))) ) : SailM (BitVec datasize) )
  (V_set rd datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (op : VBitOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3997)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3998)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3999)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand4 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let (operand1, operand2, operand3) ← (( do
    match op with
    | .VBitOp_VEOR =>
      (do
        let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
          (BitVec datasize) )
        let operand1 := (w__0 : (BitVec datasize))
        let operand2 : (BitVec datasize) := (Sail.BitVec.castWidth (Zeros (n := datasize)))
        let operand3 : (BitVec datasize) := (Sail.BitVec.castWidth (Ones (n := datasize)))
        (pure ((operand1, operand2, operand3))))
    | .VBitOp_VBSL =>
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
          (BitVec datasize) )
        let operand1 := (w__1 : (BitVec datasize))
        let operand2 : (BitVec datasize) := operand1
        let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
          (BitVec datasize) )
        let operand3 := (w__2 : (BitVec datasize))
        (pure ((operand1, operand2, operand3))))
    | .VBitOp_VBIT =>
      (do
        let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
          (BitVec datasize) )
        let operand1 := (w__3 : (BitVec datasize))
        let operand2 : (BitVec datasize) := operand1
        let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
          (BitVec datasize) )
        let operand3 := (w__4 : (BitVec datasize))
        (pure ((operand1, operand2, operand3))))
    | .VBitOp_VBIF =>
      (do
        let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read d datasize)) ) : SailM
          (BitVec datasize) )
        let operand1 := (w__5 : (BitVec datasize))
        let operand2 : (BitVec datasize) := operand1
        let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
          (BitVec datasize) )
        let operand3 := ((Complement.complement w__6) : (BitVec datasize))
        (pure ((operand1, operand2, operand3)))) ) : SailM
    ((BitVec datasize) × (BitVec datasize) × (BitVec datasize)) )
  let operand3 := operand3
  let operand2 := operand2
  let operand1 := operand1
  (V_set d datasize (Sail.BitVec.castWidth (operand1 ^^^ ((operand2 ^^^ operand4) &&& operand3))))


end ArmFull.Functions
