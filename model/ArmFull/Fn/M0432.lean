import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0041
import ArmFull.Fn.M0067
import ArmFull.Fn.M0073
import ArmFull.Fn.M0076
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0140
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0186
import ArmFull.Fn.M0196
import ArmFull.Fn.M0254

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
def VMECID_P_EL2_SysRegRead_85067caadb2f69e9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_MECEn : (BitVec 1) := (_get_SCR_EL3_Type_MECEn w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__3 ← (( do (IsCurrentSecurityState SS_Realm) ) : SailM Bool )
              if ((! w__3) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__9 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__SCR_EL3_MECEn == 0#1) : Bool))) ) : SailM Bool )
                  if (w__9 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_MECEn == 0#1)) : Bool)
                      then
                        (do
                          let w__11 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__11 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__12 ← (( do readReg VMECID_P_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_VMECID_P_EL2 w__12))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do readReg VMECID_P_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_VMECID_P_EL2 w__13)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VMPIDR_EL2_SysRegRead_6d0c680fdfd4837e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_MPIDR_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_MPIDR_EL1 w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__4 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else sailThrow ((Error_Undefined ())))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__11 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            (IsFeatureImplemented FEAT_FGT))
                        else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGRTR_EL2_MPIDR_EL1 == 1#1) : Bool)))
            ) : SailM Bool )
          if (w__11 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__12 ← (( do (EL2Enabled ()) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  let w__13 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_VMPIDR_EL2 w__13)))
              else
                (do
                  let w__14 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPIDR_EL1 w__14)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__15 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_MPIDR_EL1 w__15)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPIDR_EL1 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ZCR_EL2_SysRegRead_e12f14b3f5451ee5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_EZ : (BitVec 1) := (_get_CPTR_EL3_Type_EZ w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TZ : (BitVec 1) := (_get_CPTR_EL2_Type_TZ w__5)
  let w__6 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_ZEN : (BitVec 2) := (_get_CPTR_EL2_Type_ZEN w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__14 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__CPTR_EL3_EZ == 0#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TZ == 1#1)) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8)))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_ZEN
                           (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool))) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_EZ == 0#1)) : Bool)
                          then
                            (do
                              let w__16 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__16 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8))))
                          else
                            (do
                              let w__17 ← (( do readReg ZCR_EL2 ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_ZCR_EL2 w__17)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_EZ == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8)))
                  else
                    (do
                      let w__18 ← (( do readReg ZCR_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_ZCR_EL2 w__18))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ZCR_EL3_SysRegRead_db53f2dcbaed5b3a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_EZ : (BitVec 1) := (_get_CPTR_EL3_Type_EZ w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_EZ == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8)))
                  else
                    (do
                      let w__2 ← (( do readReg ZCR_EL3 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_ZCR_EL3 w__2))))
              else (pure (())))))


/-- Type quantifiers: k_read : Bool, t : Int -/
def AArch64_UnallocatedSysRegAccess (op0 : (BitVec 2)) (op1 : (BitVec 3)) (crn : (BitVec 4)) (op2 : (BitVec 3)) (crm : (BitVec 4)) (read : Bool) (t : Int) : SailM Unit := SailME.run do
  let rcs_el0_trap ← (( do (undefined_bool_at (← occLabel 2888) ()) ) : SailME Unit Bool )
  let tid3_trap : Bool := false
  let w__5 ← (( do
    if ((← do
         if ((← do
              (pure ((← do
                    let w__0 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                    (pure (((w__0.EL == EL1) : Bool)))) && (read : Bool)))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do readReg HCR_EL2 ) : SailME Unit (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TID3 w__4) == 1#1) : Bool))))
    else (pure false) ) : SailME Unit Bool )
  let tid3_trap ← (( do
    if (w__5 : Bool)
    then
      (do
        let w__6 ← (( do (HaveFGTExt ()) ) : SailME Unit Bool )
        if (w__6 : Bool)
        then (pure (true))
        else
          (do
            (__IMPDEF_boolean "Unallocated encodings trapped by HCR_EL2.TID3")))
    else (pure (tid3_trap)) ) : SailME Unit Bool )
  let w__14 ← (( do
    (pure ((← do
          if ((← do
               let w__9 ← (( do readReg PSTATE ) : SailME Unit ProcState )
               (pure (((w__9.EL == EL1) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              if ((← do
                   let w__10 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                   (pure (((w__10.EL == EL2) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__11 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                  (pure (((w__11.EL == EL3) : Bool)))))) && (read : Bool))) ) : SailME Unit Bool )
  if (w__14 : Bool)
  then
    (do
      if ((((op0 == 0b11#2) && (op1 == 0b000#3)) && (crn == 0b0000#4)) : Bool)
      then
        (do
          if (((crm == 0b0010#4) && (op2 == 0b111#3)) : Bool)
          then
            (do
              if (tid3_trap : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (X_set t 64 (Zeros (n := 64)))
                  SailME.throw (() : Unit)))
          else
            (do
              if (((crm == 0b0011#4) && ((op2 == 0b011#3) || ((op2 == 0b101#3) || ((op2 == 0b110#3) || (op2 == 0b111#3))))) : Bool)
              then
                (do
                  if (tid3_trap : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (X_set t 64 (Zeros (n := 64)))
                      SailME.throw (() : Unit)))
              else
                (do
                  if (((crm == 0b0100#4) && ((op2 == 0b010#3) || ((op2 == 0b011#3) || ((op2 == 0b101#3) || ((op2 == 0b110#3) || (op2 == 0b111#3)))))) : Bool)
                  then
                    (do
                      if (tid3_trap : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          (X_set t 64 (Zeros (n := 64)))
                          SailME.throw (() : Unit)))
                  else
                    (do
                      if (((crm == 0b0101#4) && ((op2 == 0b010#3) || ((op2 == 0b011#3) || ((op2 == 0b110#3) || (op2 == 0b111#3))))) : Bool)
                      then
                        (do
                          if (tid3_trap : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              (X_set t 64 (Zeros (n := 64)))
                              SailME.throw (() : Unit)))
                      else
                        (do
                          if (((crm == 0b0110#4) && ((op2 == 0b010#3) || ((op2 == 0b011#3) || ((op2 == 0b100#3) || ((op2 == 0b101#3) || ((op2 == 0b110#3) || (op2 == 0b111#3))))))) : Bool)
                          then
                            (do
                              if (tid3_trap : Bool)
                              then
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  (X_set t 64 (Zeros (n := 64)))
                                  SailME.throw (() : Unit)))
                          else
                            (do
                              if (((crm == 0b0111#4) && ((op2 == 0b011#3) || ((op2 == 0b100#3) || ((op2 == 0b101#3) || ((op2 == 0b110#3) || (op2 == 0b111#3)))))) : Bool)
                              then
                                (do
                                  if (tid3_trap : Bool)
                                  then
                                    (do
                                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                                  else
                                    (do
                                      (X_set t 64 (Zeros (n := 64)))
                                      SailME.throw (() : Unit)))
                              else (pure (()))))))))
      else (pure (())))
  else (pure (()))
  let in_feature_space : Bool :=
    ((((op0 == 0b11#2) && (let b__1 := op1
          (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 2 1)) == (0b00#2 : (BitVec 2))) : Bool)
          then true
          else
            (match b__1 with
            | 0b011 => true
            | _ => false) : Bool))) && (crn == 0b0000#4)) && (let b__2 := crm
      (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 3 3)) == (0#1 : (BitVec 1))) : Bool)
      then true
      else false : Bool)))
  let ec_val : Int := (BitVec.toNat 0x0#4)
  let w__15 ← (( do (HaveIDSExt ()) ) : SailME Unit Bool )
  let ec_val : Int :=
    if (w__15 : Bool)
    then (BitVec.toNat 0x18#8)
    else ec_val
  let ec_val : Int := ec_val
  if ((in_feature_space && read) : Bool)
  then
    (do
      let w__16 ← (( do readReg PSTATE ) : SailME Unit ProcState )
      if ((w__16.EL == EL0) : Bool)
      then
        (do
          let w__21 ← (( do
            if ((← do
                 if ((← do
                      (EL2Enabled ())) : Bool)
                 then
                   (do
                     let w__18 ← (( do (ELUsingAArch32 EL2) ) : SailME Unit Bool )
                     (pure (((! w__18) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__20 ← (( do readReg HCR_EL2 ) : SailME Unit (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_TGE w__20) == 1#1) : Bool))))
            else (pure false) ) : SailME Unit Bool )
          if (w__21 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 ec_val))
          else
            (do
              (AArch64_SystemAccessTrap EL1 ec_val)))
      else
        (do
          let w__22 ← (( do readReg PSTATE ) : SailME Unit ProcState )
          if ((w__22.EL == EL1) : Bool)
          then
            (do
              let w__27 ← (( do
                if ((← do
                     if ((← do
                          (EL2Enabled ())) : Bool)
                     then
                       (do
                         let w__24 ← (( do (ELUsingAArch32 EL2) ) : SailME Unit Bool )
                         (pure (((! w__24) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__26 ← (( do readReg HCR_EL2 ) : SailME Unit (BitVec 64) )
                    (pure ((((_get_HCR_EL2_Type_TID3 w__26) == 1#1) : Bool))))
                else (pure false) ) : SailME Unit Bool )
              if (w__27 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 ec_val))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 ec_val)))
          else
            (do
              let w__28 ← (( do readReg PSTATE ) : SailME Unit ProcState )
              if ((w__28.EL == EL2) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 ec_val))
              else
                (do
                  let w__29 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                  if ((w__29.EL == EL3) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 ec_val))
                  else (pure (()))))))
  else (pure (()))
  let w__33 ← (( do
    (pure ((← do
          if ((← do
               (HaveFeatTIDCP1 ())) : Bool)
          then
            (do
              let w__31 ← (( do readReg PSTATE ) : SailME Unit ProcState )
              (pure (((w__31.EL == EL0) : Bool))))
          else (pure false)) && (let b__0 := crn
        (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
        then true
        else false : Bool)))) ) : SailME Unit Bool )
  if (w__33 : Bool)
  then
    (do
      let w__36 ← (( do
        if ((← do
             let w__34 ← (( do (IsInHost ()) ) : SailME Unit Bool )
             (pure (((! w__34) : Bool)))) : Bool)
        then
          (do
            let w__35 ← (( do readReg SCTLR_EL1 ) : SailME Unit (BitVec 64) )
            (pure ((((_get_SCTLR_EL1_Type_TIDCP w__35) == 1#1) : Bool))))
        else (pure false) ) : SailME Unit Bool )
      if (w__36 : Bool)
      then
        (do
          let w__39 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__38 ← (( do readReg HCR_EL2 ) : SailME Unit (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_TGE w__38) == 1#1) : Bool))))
            else (pure false) ) : SailME Unit Bool )
          if (w__39 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else (pure (()))
      let w__42 ← (( do
        if ((← do
             (IsInHost ())) : Bool)
        then
          (do
            let w__41 ← (( do readReg SCTLR_EL2 ) : SailME Unit (BitVec 64) )
            (pure ((((_get_SCTLR_EL2_Type_TIDCP w__41) == 1#1) : Bool))))
        else (pure false) ) : SailME Unit Bool )
      if (w__42 : Bool)
      then
        (do
          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
      else (pure (())))
  else (pure (()))
  let w__51 ← (( do
    (pure ((← do
          (pure ((← do
                if ((← do
                     if ((← do
                          if ((← do
                               let w__43 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                               (pure (((w__43.EL == EL0) : Bool)))) : Bool)
                          then (pure true)
                          else
                            (do
                              let w__44 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                              (pure (((w__44.EL == EL1) : Bool))))) : Bool)
                     then
                       (do
                         (EL2Enabled ()))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__48 ← (( do readReg HCR_EL2 ) : SailME Unit (BitVec 64) )
                    (pure ((((_get_HCR_EL2_Type_TIDCP w__48) == 1#1) : Bool))))
                else (pure false)) && (((op0 == 0b01#2) || (op0 == 0b11#2)) : Bool)))) && (((crn == 0b1011#4) || (crn == 0b1111#4)) : Bool)))
    ) : SailME Unit Bool )
  if (w__51 : Bool)
  then
    (do
      let rcs_el0_trap ← (( do (__IMPDEF_boolean "Reserved Control Space EL0 Trapped") ) : SailME
        Unit Bool )
      let w__53 ← (( do
        (pure ((← do
              let w__52 ← (( do readReg PSTATE ) : SailME Unit ProcState )
              (pure (((w__52.EL == EL1) : Bool)))) || rcs_el0_trap)) ) : SailME Unit Bool )
      if (w__53 : Bool)
      then
        (do
          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
      else (pure (())))
  else (pure (()))
  if (((((Sail.BitVec.castWidth (m := 2) (BitVec.slice op0 0 2)) == 0b01#2) || ((Sail.BitVec.castWidth (m := 2) (BitVec.slice
             op0 0 2)) == 0b11#2)) && (((Sail.BitVec.castWidth (m := 4) (BitVec.slice crn 0 4)) == 0b1011#4) || ((Sail.BitVec.castWidth (m := 4) (BitVec.slice
             crn 0 4)) == 0b1111#4))) : Bool)
  then sailThrow ((Error_ImplementationDefined ""))
  else (pure (()))
  let rcs_el0_trap := rcs_el0_trap
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def ACCDATA_EL1_SysRegWrite_8e0ffec0877851f7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ADEn : (BitVec 1) := (_get_SCR_EL3_Type_ADEn w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_nACCDATA_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_nACCDATA_EL1 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_ADEn == 0#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__15 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGWTR_EL2_nACCDATA_EL1 == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__15 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_ADEn == 0#1)) : Bool)
                  then
                    (do
                      let w__17 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__17 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__18 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ACCDATA_EL1 (Mk_ACCDATA_EL1_Type w__18)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__24 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_ADEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__24 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_ADEn == 0#1)) : Bool)
                  then
                    (do
                      let w__26 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__26 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ACCDATA_EL1 (Mk_ACCDATA_EL1_Type w__27))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__28 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg ACCDATA_EL1 (Mk_ACCDATA_EL1_Type w__28))
              else (pure (())))))


end ArmFull.Functions
