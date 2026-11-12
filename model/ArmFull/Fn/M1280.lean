import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0050
import ArmFull.Fn.M0058
import ArmFull.Fn.M0063
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0124
import ArmFull.Fn.M0146
import ArmFull.Fn.M0166
import ArmFull.Fn.M0175
import ArmFull.Fn.M0181
import ArmFull.Fn.M0254
import ArmFull.Fn.M1174
import ArmFull.Fn.M1175
import ArmFull.Fn.M1176

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

/-- Type quantifiers: t : Int, t2 : Int -/
def VTTBR_EL2_SysRegWrite128_3ec09d9d33270957 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__5) +++ (_get_HCR_EL2_Type_NV w__6)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let w__8 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
              let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set__1 (BitVec.toNat 0x020#12) 128 (w__8 +++ w__9)))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__17 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
              if (w__17 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      let w__19 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__19 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      let w__20 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
                      let w__21 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                      let w__22 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (VTTBR_EL2_write
                        (Mk_VTTBR_EL2_Type
                          (Sail.BitVec.updateSubrange w__20 127 0 (w__21 +++ w__22)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
                  let w__24 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                  let w__25 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (VTTBR_EL2_write
                    (Mk_VTTBR_EL2_Type (Sail.BitVec.updateSubrange w__23 127 0 (w__24 +++ w__25)))))
              else (pure (())))))


def decode_aarch32_instrs_LDM_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:3589.29-3589.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDM_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDM_T1enc_A_txt (Rn : (BitVec 3)) (register_list : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := (0b00000000#8 +++ register_list)
      let wback : Bool :=
        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers (Sail.Int.toNatChecked (n)))])) == 0#1)
      if (((BitCount registers) <b 1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDM_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDM_T2enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (P : (BitVec 1)) (M : (BitVec 1)) (register_list : (BitVec 14)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := ((P +++ M) +++ register_list)
      let wback : Bool := (W == 1#1)
      if ((((n == 15) || ((BitCount registers) <b 2)) || ((P == 1#1) && (M == 1#1))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 13)])) == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__4 ← (( do
        if ((← do
             if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 15)])) == 1#1) : Bool) : Bool)
             then
               (do
                 (InITBlock ()))
             else (pure false)) : Bool)
        then
          (do
            let w__3 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDM_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDMDA_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:3697.29-3697.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDMDA_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDMDB_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:3749.29-3749.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDMDB_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDMDB_T1enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (P : (BitVec 1)) (M : (BitVec 1)) (register_list : (BitVec 14)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := ((P +++ M) +++ register_list)
      let wback : Bool := (W == 1#1)
      if ((((n == 15) || ((BitCount registers) <b 2)) || ((P == 1#1) && (M == 1#1))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 13)])) == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__4 ← (( do
        if ((← do
             if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 15)])) == 1#1) : Bool) : Bool)
             then
               (do
                 (InITBlock ()))
             else (pure false)) : Bool)
        then
          (do
            let w__3 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDMDB_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDMIB_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:3835.29-3835.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDMIB_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDRB_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:3881.29-3881.30"
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRB (literal)"))
      else (pure (()))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRBT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || (wback && (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRB_i_OpA_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRB_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm5 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRB_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRB_i_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLD"))
      else (pure (()))
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRB (literal)"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRB_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRB_i_T3enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((((Rt == 0b1111#4) && (P == 1#1)) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "PLD, PLDW (immediate)"))
      else (pure (()))
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRB (literal)"))
      else (pure (()))
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "LDRBT"))
      else (pure (()))
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((((t == 15) && (W == 1#1)) || (wback && (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRB_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRB_l_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:4041.29-4041.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRBT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || wback) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRB_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRB_l_T1enc_A_txt (U : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLD"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_LDRB_l_Op_A_txt add imm32 (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRB_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:4114.29-4114.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3028) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3029) ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRBT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRB_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRB_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3030) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3031) ()) ) : SailM SRType )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_LDRB_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRB_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3032) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3033) ()) ) : SailM SRType )
      if ((Rt == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLD"))
      else (pure (()))
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRB (literal)"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRB_r_Op_A_txt add index (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRBT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:4246.29-4246.30"
      let m ← (( do (undefined_int_at (← occLabel 3034) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3035) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3036) ()) ) : SailM SRType )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      if ((((t == 15) || (n == 15)) || (n == t)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      let m : Int := m
      (execute_aarch32_instrs_LDRBT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form shift_n shift_t (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRBT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:4281.29-4281.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3037) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3038) ()) ) : SailM SRType )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3039) 32) ) : SailM (BitVec 32) )
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((((t == 15) || (n == 15)) || (n == t)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let imm32 := imm32
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_LDRBT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form shift_n shift_t (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRBT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m ← (( do (undefined_int_at (← occLabel 3040) ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int_at (← occLabel 3041) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3042) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRB (literal)"))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      let m : Int := m
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRBT_Op_A_txt add imm32 m (Sail.Int.toNatChecked (n)) postindex
        register_form shift_n shift_t (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_LDRD_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:4383.29-4383.30"
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRD (literal)"))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Rt 0)])) == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (t +i 1)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((n == t) || (n == t2))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((t2 == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRD_i_Op_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRD_i_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRD (literal)"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let t2 : Int := (BitVec.toNat Rt2)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((wback && ((n == t) || (n == t2))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((((t == 15) || (t2 == 15)) || (t == t2)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRD_i_Op_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) wback))
  else (pure (()))


end ArmFull.Functions
