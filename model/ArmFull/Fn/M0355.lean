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
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0170
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
def MPAMSM_EL1_SysRegRead_8b218aacc540b1cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  let __MPAM3_EL3_TRAPLOWER : (BitVec 1) := (_get_MPAM3_EL3_Type_TRAPLOWER w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  let __MPAM2_EL2_EnMPAMSM : (BitVec 1) := (_get_MPAM2_EL2_Type_EnMPAMSM w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__7 ← (( do
                (pure ((← do
                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
              if (w__7 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__9 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__MPAM2_EL2_EnMPAMSM == 0#1) : Bool))) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__10 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPAMSM_EL1 w__10)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do
                (pure ((← do
                      (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                  if (w__14 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__15 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPAMSM_EL1 w__15))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPAMSM_EL1 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MVFR0_EL1_SysRegRead_dd15ac4d4e4917f3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__3 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
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
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__8 ← (( do readReg MVFR0_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__8)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg MVFR0_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__9))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg MVFR0_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 w__10))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MVFR1_EL1_SysRegRead_ac66b9abd61faeb2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__3 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
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
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__8 ← (( do readReg MVFR1_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__8)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg MVFR1_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__9))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg MVFR1_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 w__10))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MVFR2_EL1_SysRegRead_56cfaa06768c8d8a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__3 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
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
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__8 ← (( do readReg MVFR2_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__8)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg MVFR2_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__9))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg MVFR2_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 w__10))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def OSDLR_EL1_SysRegRead_b4a733586ba54671 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_OSDLR_EL1 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_OSDLR_EL1 w__1)
  let w__2 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TDOSA : (BitVec 1) := (_get_MDCR_EL2_Type_TDOSA w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__15 ← (( do
            if ((← do
                 if ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    (HaveEL EL3))
                                else (pure false)) : Bool)
                           then
                             (do
                               let w__6 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                               (pure ((((_get_EDSCR_Type_SDD w__6) == 1#1) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__10 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                     (pure ((((_get_MDCR_EL3_Type_TDOSA w__10) == 1#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                if ((← do
                     (IsFeatureImplemented FEAT_DoubleLock)) : Bool)
                then (pure true)
                else
                  (do
                    (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA")))
            else (pure false) ) : SailM Bool )
          if (w__15 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__25 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) : Bool)
                           then
                             (do
                               if ((← do
                                    let w__19 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__19) : Bool)))) : Bool)
                               then (pure true)
                               else
                                 (do
                                   let w__20 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                   (pure ((((_get_SCR_EL3_Type_FGTEn w__20) == 1#1) : Bool)))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (IsFeatureImplemented FEAT_DoubleLock))
                      else (pure false)) && ((__HDFGRTR_EL2_OSDLR_EL1 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__25 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__33 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__27 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                             let w__28 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                             (pure (((((_get_MDCR_EL2_Type_TDE w__27) +++ (_get_MDCR_EL2_Type_TDOSA
                                     w__28)) != 0b00#2) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        if ((← do
                             (IsFeatureImplemented FEAT_DoubleLock)) : Bool)
                        then (pure true)
                        else
                          (do
                            (__IMPDEF_boolean "Trapped by MDCR_EL2.TDOSA")))
                    else (pure false) ) : SailM Bool )
                  if (w__33 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__40 ← (( do
                        if ((← do
                             if ((← do
                                  (HaveEL EL3)) : Bool)
                             then
                               (do
                                 let w__35 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((_get_MDCR_EL3_Type_TDOSA w__35) == 1#1) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            if ((← do
                                 (IsFeatureImplemented FEAT_DoubleLock)) : Bool)
                            then (pure true)
                            else
                              (do
                                (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA")))
                        else (pure false) ) : SailM Bool )
                      if (w__40 : Bool)
                      then
                        (do
                          let w__43 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__42 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__42) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__43 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__44 ← (( do readReg OSDLR_EL1 ) : SailM (BitVec 64) )
                          let w__45 ← (( do (__get_OSDLR_EL1 w__44) ) : SailM (BitVec 64) )
                          (X_set t 64 w__45))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__58 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        (HaveEL EL3))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   let w__49 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                   (pure ((((_get_EDSCR_Type_SDD w__49) == 1#1) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__53 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_MDCR_EL3_Type_TDOSA w__53) == 1#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    if ((← do
                         (IsFeatureImplemented FEAT_DoubleLock)) : Bool)
                    then (pure true)
                    else
                      (do
                        (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA")))
                else (pure false) ) : SailM Bool )
              if (w__58 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__65 ← (( do
                    if ((← do
                         if ((← do
                              (HaveEL EL3)) : Bool)
                         then
                           (do
                             let w__60 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((_get_MDCR_EL3_Type_TDOSA w__60) == 1#1) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        if ((← do
                             (IsFeatureImplemented FEAT_DoubleLock)) : Bool)
                        then (pure true)
                        else
                          (do
                            (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA")))
                    else (pure false) ) : SailM Bool )
                  if (w__65 : Bool)
                  then
                    (do
                      let w__68 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__67 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__67) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__68 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__69 ← (( do readReg OSDLR_EL1 ) : SailM (BitVec 64) )
                      let w__70 ← (( do (__get_OSDLR_EL1 w__69) ) : SailM (BitVec 64) )
                      (X_set t 64 w__70))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__71 ← (( do readReg OSDLR_EL1 ) : SailM (BitVec 64) )
                  let w__72 ← (( do (__get_OSDLR_EL1 w__71) ) : SailM (BitVec 64) )
                  (X_set t 64 w__72))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def OSDTRRX_EL1_SysRegRead_ed7388c985c3d430 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDCC : (BitVec 1) := (_get_MDCR_EL3_Type_TDCC w__2)
  let w__3 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__3)
  let w__4 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TDCC : (BitVec 1) := (_get_MDCR_EL2_Type_TDCC w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__7 ← (( do
        if ((← do
             (Halted ())) : Bool)
        then
          (do
            (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG))
        else (pure false) ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          let w__8 ← (( do readReg OSDTRRX_EL1 ) : SailM (BitVec 64) )
          (X_set t 64 (__get_OSDTRRX_EL1 w__8)))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__15 ← (( do
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
                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__15 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__22 ← (( do
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
                  if (w__22 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__24 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool
                        )
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
                                (pure (((((_get_MDCR_EL2_Type_TDE w__26) +++ (_get_MDCR_EL2_Type_TDA
                                        w__27)) != 0b00#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__28 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__30 : Bool)
                              then
                                (do
                                  let w__32 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__32 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__34 ← (( do
                                    (pure ((← do
                                          (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__34 : Bool)
                                  then
                                    (do
                                      let w__36 ← (( do
                                        (pure ((← do
                                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) :
                                        SailM Bool )
                                      if (w__36 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                  else
                                    (do
                                      let w__37 ← (( do readReg OSDTRRX_EL1 ) : SailM (BitVec 64)
                                        )
                                      (X_set t 64 (__get_OSDTRRX_EL1 w__37)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__44 ← (( do
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
                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__44 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__51 ← (( do
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
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__51 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__53 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__53 : Bool)
                          then
                            (do
                              let w__55 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__55 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__57 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__57 : Bool)
                              then
                                (do
                                  let w__59 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__59 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__60 ← (( do readReg OSDTRRX_EL1 ) : SailM (BitVec 64) )
                                  (X_set t 64 (__get_OSDTRRX_EL1 w__60)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__61 ← (( do readReg OSDTRRX_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_OSDTRRX_EL1 w__61)))
                  else (pure (()))))))


end ArmFull.Functions
