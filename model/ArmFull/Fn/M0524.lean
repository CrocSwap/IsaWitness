module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0071
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0075
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0175
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0252 set_option backward.proofsInPublic true @[expose] public section

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
def RCWMASK_EL1_SysRegWrite_41a34d24e689c9c2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_RCWMASKEn : (BitVec 1) := (_get_SCR_EL3_Type_RCWMASKEn w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_nRCWMASK_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_nRCWMASK_EL1 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__11 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             if ((← do
                                  (Halted ())) : Bool)
                             then
                               (do
                                 (HaveEL EL3))
                             else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__18 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT))
                           else (pure false)) : Bool)
                      then
                        (do
                          (pure ((← do
                                let w__15 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__15) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGWTR_EL2_nRCWMASK_EL1 == 0#1) : Bool))) ) : SailM
                Bool )
              if (w__18 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__20 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
                  if (w__20 : Bool)
                  then
                    (do
                      let w__22 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__22 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__23 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                      let w__24 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__23 63 0 w__24)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__31 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__31 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__33 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
                  if (w__33 : Bool)
                  then
                    (do
                      let w__35 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__35 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__36 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                      let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__36 63 0 w__37))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__38 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                  let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__38 63 0 w__39))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def RCWSMASK_EL1_SysRegWrite_ac52083fadb4f430 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_RCWMASKEn : (BitVec 1) := (_get_SCR_EL3_Type_RCWMASKEn w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__3)
  let w__4 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR2_EL2_nRCWSMASK_EL1 : (BitVec 1) := (_get_HFGWTR2_EL2_Type_nRCWSMASK_EL1 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__11 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             if ((← do
                                  (Halted ())) : Bool)
                             then
                               (do
                                 (HaveEL EL3))
                             else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__17 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT2))
                           else (pure false)) : Bool)
                      then
                        (do
                          (HaveEL EL3))
                      else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__17 : Bool)
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
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HFGWTR2_EL2_nRCWSMASK_EL1 == 0#1) : Bool))) ) :
                    SailM Bool )
                  if (w__21 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__23 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__23 : Bool)
                      then
                        (do
                          let w__25 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__25 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__26 ← (( do readReg RCWSMASK_EL1 ) : SailM (BitVec 128) )
                          let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange w__26 63 0 w__27))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__34 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__34 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__36 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
                  if (w__36 : Bool)
                  then
                    (do
                      let w__38 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__38 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__39 ← (( do readReg RCWSMASK_EL1 ) : SailM (BitVec 128) )
                      let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange w__39 63 0 w__40))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__41 ← (( do readReg RCWSMASK_EL1 ) : SailM (BitVec 128) )
                  let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange w__41 63 0 w__42))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def RGSR_EL1_SysRegWrite_bd35adfccbaf05b5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ATA : (BitVec 1) := (_get_SCR_EL3_Type_ATA w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_ATA : (BitVec 1) := (_get_HCR_EL2_Type_ATA w__3)
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
                             if ((← do
                                  (Halted ())) : Bool)
                             then
                               (do
                                 (HaveEL EL3))
                             else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_ATA == 0#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_ATA == 0#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_ATA == 0#1) : Bool))) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__16 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__16 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__17 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg RGSR_EL1 (Mk_RGSR_EL1_Type w__17)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__24 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_ATA == 0#1) : Bool))) ) : SailM Bool )
              if (w__24 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__26 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_ATA == 0#1) : Bool))) ) : SailM Bool )
                  if (w__26 : Bool)
                  then
                    (do
                      let w__28 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__28 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__29 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg RGSR_EL1 (Mk_RGSR_EL1_Type w__29))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__30 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg RGSR_EL1 (Mk_RGSR_EL1_Type w__30))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def RMR_EL2_SysRegWrite_fb0b01388c042301 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__0)
  let w__6 ← (( do
    (pure ((← do
          if ((← do
               if ((← do
                    let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__1.EL == EL1) : Bool)))) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              (IsHighestEL EL2))
          else (pure false)) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
  else
    (do
      let w__9 ← (( do
        if ((← do
             let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__7.EL == EL2) : Bool)))) : Bool)
        then
          (do
            (IsHighestEL EL2))
        else (pure false) ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg RMR_EL2 (Mk_RMR_EL2_Type w__10))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def S3_op1_Cn_Cm_op2_SysRegWrite_7b9e3d26ebc2fd52 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_TIDCP : (BitVec 1) := (_get_SCTLR_EL1_Type_TIDCP w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_TIDCP : (BitVec 1) := (_get_SCTLR_EL2_Type_TIDCP w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TIDCP : (BitVec 1) := (_get_HCR_EL2_Type_TIDCP w__4)
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
              (pure (((! w__8) : Bool)))) && ((__SCTLR_EL1_TIDCP == 1#1) : Bool))) ) : SailM Bool )
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
                  else (pure false)) && ((__SCTLR_EL2_TIDCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_ImpDefSysRegWrite op0 op1 CRn CRm op2 t))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__18 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TIDCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_ImpDefSysRegWrite op0 op1 CRn CRm op2 t)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              (AArch64_ImpDefSysRegWrite op0 op1 CRn CRm op2 t))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (AArch64_ImpDefSysRegWrite op0 op1 CRn CRm op2 t))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SCTLR2_EL2_SysRegWrite_5e16f7d77f725c0b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_SCTLR2En : (BitVec 1) := (_get_SCR_EL3_Type_SCTLR2En w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_SCTLR2En == 0#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_SCTLR2En == 0#1) : Bool))) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__16 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__16 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__17 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg SCTLR2_EL2 (Mk_SCTLR2_EL2_Type w__17))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__18 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SCTLR2_EL2 (Mk_SCTLR2_EL2_Type w__18))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SCTLR_EL2_SysRegWrite_3de2374320961a12 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (__set_SCTLR_EL2 (Mk_SCTLR_EL2_Type w__4)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (__set_SCTLR_EL2 (Mk_SCTLR_EL2_Type w__5)))
              else (pure (())))))


end ArmFull.Functions
