module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0139
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0144
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
def DBGCLAIMCLR_EL1_SysRegRead_ffbb497475eb383a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_DBGCLAIM : (BitVec 1) := (_get_HDFGRTR_EL2_Type_DBGCLAIM w__4)
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
                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
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
                      else (pure false)) && ((__HDFGRTR_EL2_DBGCLAIM == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__18 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__22 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__20 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__21 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__20) +++ (_get_MDCR_EL2_Type_TDA w__21)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__24 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__24 : Bool)
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
                          let w__27 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_DBGCLAIMCLR_EL1 w__27)))))))
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
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__34 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__36 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
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
                      let w__39 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_DBGCLAIMCLR_EL1 w__39)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__40 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_DBGCLAIMCLR_EL1 w__40)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGCLAIMSET_EL1_SysRegRead_e478959c32681458 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_DBGCLAIM : (BitVec 1) := (_get_HDFGRTR_EL2_Type_DBGCLAIM w__4)
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
                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
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
                      else (pure false)) && ((__HDFGRTR_EL2_DBGCLAIM == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__18 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__22 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__20 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__21 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__20) +++ (_get_MDCR_EL2_Type_TDA w__21)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__24 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__24 : Bool)
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
                          let w__27 ← (( do readReg DBGCLAIMSET_EL1 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_DBGCLAIMSET_EL1 w__27)))))))
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
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__34 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__36 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
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
                      let w__39 ← (( do readReg DBGCLAIMSET_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_DBGCLAIMSET_EL1 w__39)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__40 ← (( do readReg DBGCLAIMSET_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_DBGCLAIMSET_EL1 w__40)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGDTRRX_EL0_SysRegRead_54d73d4619fa5dbf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let __MDSCR_EL1_TDCC : (BitVec 1) := (_get_MDSCR_EL1_Type_TDCC w__1)
  let w__2 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TDCC : (BitVec 1) := (_get_MDCR_EL2_Type_TDCC w__2)
  let w__3 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDCC : (BitVec 1) := (_get_MDCR_EL3_Type_TDCC w__3)
  let w__4 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__4)
  let w__5 ← (( do (Halted ()) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__6 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
      (X_set t 64 (__get_DBGDTRRX_EL0 w__6)))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if ((__MDSCR_EL1_TDCC == 1#1) : Bool)
          then
            (do
              let w__9 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HCR_EL2_Type_TGE w__8) == 1#1) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__17 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        if ((← do
                             let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                             (pure ((((_get_HCR_EL2_Type_TGE w__13) == 1#1) : Bool)))) : Bool)
                        then (pure true)
                        else
                          (do
                            let w__14 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__15 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__14) +++ (_get_MDCR_EL2_Type_TDA
                                    w__15)) != 0b00#2) : Bool)))))
                    else (pure false) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__19 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__19 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__21 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__21 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__22 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_DBGDTRRX_EL0 w__22))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__24 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__24 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__28 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__26 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__27 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__26) +++ (_get_MDCR_EL2_Type_TDA w__27)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__28 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__30 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__30 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__32 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__32 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__33 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_DBGDTRRX_EL0 w__33)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__35 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__35 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__37 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__37 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__38 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_DBGDTRRX_EL0 w__38)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__39 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_DBGDTRRX_EL0 w__39)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGDTR_EL0_SysRegRead_59f5860954a90673 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let __MDSCR_EL1_TDCC : (BitVec 1) := (_get_MDSCR_EL1_Type_TDCC w__1)
  let w__2 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TDCC : (BitVec 1) := (_get_MDCR_EL2_Type_TDCC w__2)
  let w__3 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDCC : (BitVec 1) := (_get_MDCR_EL3_Type_TDCC w__3)
  let w__4 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__4)
  let w__5 ← (( do (Halted ()) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__6 ← (( do (DBGDTR_EL0_read__1 ()) ) : SailM (BitVec 64) )
      (X_set t 64 w__6))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          if ((__MDSCR_EL1_TDCC == 1#1) : Bool)
          then
            (do
              let w__9 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HCR_EL2_Type_TGE w__8) == 1#1) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__17 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        if ((← do
                             let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                             (pure ((((_get_HCR_EL2_Type_TGE w__13) == 1#1) : Bool)))) : Bool)
                        then (pure true)
                        else
                          (do
                            let w__14 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__15 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__14) +++ (_get_MDCR_EL2_Type_TDA
                                    w__15)) != 0b00#2) : Bool)))))
                    else (pure false) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__19 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__19 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__21 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__21 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__22 ← (( do (DBGDTR_EL0_read__1 ()) ) : SailM (BitVec 64) )
                              (X_set t 64 w__22)))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__24 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__24 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__28 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__26 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__27 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__26) +++ (_get_MDCR_EL2_Type_TDA w__27)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__28 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__30 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__30 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__32 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__32 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__33 ← (( do (DBGDTR_EL0_read__1 ()) ) : SailM (BitVec 64) )
                              (X_set t 64 w__33))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__35 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__35 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__37 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__37 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__38 ← (( do (DBGDTR_EL0_read__1 ()) ) : SailM (BitVec 64) )
                          (X_set t 64 w__38))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__39 ← (( do (DBGDTR_EL0_read__1 ()) ) : SailM (BitVec 64) )
                      (X_set t 64 w__39))
                  else (pure (()))))))


end ArmFull.Functions
