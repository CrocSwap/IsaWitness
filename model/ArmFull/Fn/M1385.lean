import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0048
import ArmFull.Fn.M0071
import ArmFull.Fn.M0074
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0146
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0254
import ArmFull.Fn.M1278

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
def CNTHV_CVAL_EL2_SysRegWrite_16bd78456d53d9ab (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0VTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0VTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0VTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0VTEN w__3)
  let w__4 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1TVT : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1TVT w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__9 ← (( do
        (pure ((← do
              let w__8 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__6) +++ (_get_HCR_EL2_Type_TGE w__7)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__8) : Bool)))) && ((__CNTKCTL_EL1_EL0VTEN == 0#1) : Bool))) ) : SailM
        Bool )
      if (w__9 : Bool)
      then
        (do
          let w__11 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__13) +++ (_get_HCR_EL2_Type_TGE w__14)) == 0b11#2) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL0VTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__21 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__18) +++ (_get_HCR_EL2_Type_TGE w__19)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__21 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__29 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__23) +++ (_get_HCR_EL2_Type_TGE
                                          w__24)) == 0b11#2) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             let w__26 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((_get_SCR_EL3_Type_NS w__26) == 0#1) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        (IsFeatureImplemented FEAT_SEL2))
                    else (pure false) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      let w__30 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type w__30))
                  else
                    (do
                      let w__36 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure (((((_get_HCR_EL2_Type_E2H w__32) +++ (_get_HCR_EL2_Type_TGE
                                         w__33)) == 0b11#2) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__35 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure ((((_get_SCR_EL3_Type_NS w__35) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__36 : Bool)
                      then
                        (do
                          let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type w__37))
                      else
                        (do
                          let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type w__38)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__40 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool )
          if (w__40 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__45 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__42) +++ ((_get_HCR_EL2_Type_NV1 w__43) +++ (_get_HCR_EL2_Type_NV
                              w__44))) == 0b111#3) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__45 : Bool)
              then
                (do
                  let w__46 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (NVMem_set (BitVec.toNat 0x168#12) w__46))
              else
                (do
                  let w__47 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type w__47))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__52 ← (( do
                if ((← do
                     if ((← do
                          let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_E2H w__48) == 1#1) : Bool)))) : Bool)
                     then
                       (do
                         let w__49 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_SCR_EL3_Type_NS w__49) == 0#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    (IsFeatureImplemented FEAT_SEL2))
                else (pure false) ) : SailM Bool )
              if (w__52 : Bool)
              then
                (do
                  let w__53 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type w__53))
              else
                (do
                  let w__56 ← (( do
                    if ((← do
                         let w__54 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         (pure ((((_get_HCR_EL2_Type_E2H w__54) == 1#1) : Bool)))) : Bool)
                    then
                      (do
                        let w__55 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        (pure ((((_get_SCR_EL3_Type_NS w__55) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__56 : Bool)
                  then
                    (do
                      let w__57 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type w__57))
                  else
                    (do
                      let w__58 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type w__58))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__59 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type w__59))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTPOFF_EL2_SysRegWrite_daa2a43614202ee5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ECVEn : (BitVec 1) := (_get_SCR_EL3_Type_ECVEn w__3)
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
              let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x1A8#12) w__8))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__16 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_ECVEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_ECVEn == 0#1)) : Bool)
                  then
                    (do
                      let w__18 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__18 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__19 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CNTPOFF_EL2 w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTPOFF_EL2 w__20)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTP_CTL_EL0_SysRegWrite_6000d5c756b25763 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1NVPCT : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1NVPCT w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__5) +++ ((_get_HCR_EL2_Type_NV1 w__6) +++ (_get_HCR_EL2_Type_NV
                          w__7))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              let w__13 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__10) +++ (_get_HCR_EL2_Type_TGE w__11)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1NVPCT == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (NVMem_set (BitVec.toNat 0x180#12) w__14)))
          else
            (do
              let w__16 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__17 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (__set_CNTP_CTL_EL0 (Mk_CNTP_CTL_EL0_Type w__17)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__21 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__19 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__19) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__21 : Bool)
                  then
                    (do
                      let w__22 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (__set_CNTP_CTL_EL0 (Mk_CNTP_CTL_EL0_Type w__22)))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTP_CVAL_EL0_SysRegWrite_226b60eb1c89b722 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1NVPCT : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1NVPCT w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__5) +++ ((_get_HCR_EL2_Type_NV1 w__6) +++ (_get_HCR_EL2_Type_NV
                          w__7))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              let w__13 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__10) +++ (_get_HCR_EL2_Type_TGE w__11)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1NVPCT == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (NVMem_set (BitVec.toNat 0x178#12) w__14)))
          else
            (do
              let w__16 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__17 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type w__17))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__21 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__19 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__19) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__21 : Bool)
                  then
                    (do
                      let w__22 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type w__22))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTVOFF_EL2_SysRegWrite_926108484bd738bb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__3) +++ (_get_HCR_EL2_Type_NV w__4)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x060#12) w__6))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg CNTVOFF_EL2 w__9)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTVOFF_EL2 w__10)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTV_CTL_EL0_SysRegWrite_18ae5268f90eea09 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1NVVCT : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1NVVCT w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__5) +++ ((_get_HCR_EL2_Type_NV1 w__6) +++ (_get_HCR_EL2_Type_NV
                          w__7))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              let w__13 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__10) +++ (_get_HCR_EL2_Type_TGE w__11)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1NVVCT == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (NVMem_set (BitVec.toNat 0x170#12) w__14)))
          else
            (do
              let w__16 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__17 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (__set_CNTV_CTL_EL0 (Mk_CNTV_CTL_EL0_Type w__17)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__21 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__19 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__19) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__21 : Bool)
                  then
                    (do
                      let w__22 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (__set_CNTV_CTL_EL0 (Mk_CNTV_CTL_EL0_Type w__22)))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


end ArmFull.Functions
