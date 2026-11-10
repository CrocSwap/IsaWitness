import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0041
import ArmFull.Fn.M0044
import ArmFull.Fn.M0045
import ArmFull.Fn.M0064
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0113
import ArmFull.Fn.M0146
import ArmFull.Fn.M0166
import ArmFull.Fn.M0181
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
def MPAMSM_EL1_SysRegWrite_2a763b1f04834a78 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
          then
            (do
              let w__5 ← (( do
                (pure ((← do
                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
              if (w__5 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__7 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__MPAM2_EL2_EnMPAMSM == 0#1) : Bool))) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMSM_EL1 (Mk_MPAMSM_EL1_Type w__8))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if (((HaveEL EL3) && (__MPAM3_EL3_TRAPLOWER == 1#1)) : Bool)
              then
                (do
                  let w__10 ← (( do
                    (pure ((← do
                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                  if (w__10 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMSM_EL1 (Mk_MPAMSM_EL1_Type w__11)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MPAMSM_EL1 (Mk_MPAMSM_EL1_Type w__12))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def OSDLR_EL1_SysRegWrite_3d852917a7f252a5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_OSDLR_EL1 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_OSDLR_EL1 w__1)
  let w__2 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TDOSA : (BitVec 1) := (_get_MDCR_EL2_Type_TDOSA w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__14 ← (( do
            if ((← do
                 if ((← do
                      if ((← do
                           if ((← do
                                (pure ((← do
                                      (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                           then
                             (do
                               let w__5 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                               (pure ((((_get_EDSCR_Type_SDD w__5) == 1#1) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__9 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                     (pure ((((_get_MDCR_EL3_Type_TDOSA w__9) == 1#1) : Bool))))
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
          if (w__14 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__23 ← (( do
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
                               if (((! (HaveEL EL3)) : Bool) : Bool)
                               then (pure true)
                               else
                                 (do
                                   let w__18 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                   (pure ((((_get_SCR_EL3_Type_FGTEn w__18) == 1#1) : Bool)))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (IsFeatureImplemented FEAT_DoubleLock))
                      else (pure false)) && ((__HDFGWTR_EL2_OSDLR_EL1 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__23 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__31 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__25 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                             let w__26 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                             (pure (((((_get_MDCR_EL2_Type_TDE w__25) +++ (_get_MDCR_EL2_Type_TDOSA
                                     w__26)) != 0b00#2) : Bool))))
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
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__37 ← (( do
                        if ((← do
                             if (((HaveEL EL3) : Bool) : Bool)
                             then
                               (do
                                 let w__32 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((_get_MDCR_EL3_Type_TDOSA w__32) == 1#1) : Bool))))
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
                      if (w__37 : Bool)
                      then
                        (do
                          let w__40 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__39 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__39) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__40 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg OSDLR_EL1 (Mk_OSDLR_EL1_Type w__41))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__53 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               if ((← do
                                    (pure ((← do
                                          (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                               then
                                 (do
                                   let w__44 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                   (pure ((((_get_EDSCR_Type_SDD w__44) == 1#1) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__48 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_MDCR_EL3_Type_TDOSA w__48) == 1#1) : Bool))))
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
              if (w__53 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__59 ← (( do
                    if ((← do
                         if (((HaveEL EL3) : Bool) : Bool)
                         then
                           (do
                             let w__54 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((_get_MDCR_EL3_Type_TDOSA w__54) == 1#1) : Bool))))
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
                  if (w__59 : Bool)
                  then
                    (do
                      let w__62 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__61 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__61) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__62 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__63 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg OSDLR_EL1 (Mk_OSDLR_EL1_Type w__63))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__64 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg OSDLR_EL1 (Mk_OSDLR_EL1_Type w__64))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def OSDTRRX_EL1_SysRegWrite_8dcacb00f53cccfe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg OSDTRRX_EL1 w__8)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
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
                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__20 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__20 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__22 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__26 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__24 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                let w__25 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_MDCR_EL2_Type_TDE w__24) +++ (_get_MDCR_EL2_Type_TDA
                                        w__25)) != 0b00#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__26 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then
                                (do
                                  let w__28 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__28 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                  then
                                    (do
                                      let w__30 ← (( do
                                        (pure ((← do
                                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) :
                                        SailM Bool )
                                      if (w__30 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                  else
                                    (do
                                      let w__31 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg OSDTRRX_EL1 w__31)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__37 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__37 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__43 ← (( do
                        (pure ((← do
                              if ((← do
                                   (pure ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                              then
                                (do
                                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__43 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                          then
                            (do
                              let w__45 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__45 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                              then
                                (do
                                  let w__47 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__47 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__48 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg OSDTRRX_EL1 w__48)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__49 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg OSDTRRX_EL1 w__49)
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def OSDTRTX_EL1_SysRegWrite_a6594f8c79e7c726 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg OSDTRTX_EL1 w__8)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
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
                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__20 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__20 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__22 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__26 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__24 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                let w__25 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_MDCR_EL2_Type_TDE w__24) +++ (_get_MDCR_EL2_Type_TDA
                                        w__25)) != 0b00#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__26 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                              then
                                (do
                                  let w__28 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__28 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                                  then
                                    (do
                                      let w__30 ← (( do
                                        (pure ((← do
                                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) :
                                        SailM Bool )
                                      if (w__30 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                  else
                                    (do
                                      let w__31 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg OSDTRTX_EL1 w__31)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__37 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__37 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__43 ← (( do
                        (pure ((← do
                              if ((← do
                                   (pure ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                              then
                                (do
                                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__43 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDCC == 1#1)) : Bool)
                          then
                            (do
                              let w__45 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__45 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                              then
                                (do
                                  let w__47 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__47 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__48 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg OSDTRTX_EL1 w__48)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__49 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg OSDTRTX_EL1 w__49)
                  else (pure (()))))))


end ArmFull.Functions
