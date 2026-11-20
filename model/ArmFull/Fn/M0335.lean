module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0185
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0244
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
def DBGWVR_EL1_SysRegRead_469f2550ef085d68 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 w__4)
  let w__5 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__5)
  let w__13 ← (( do
    if ((← do
         if ((← do
              let w__6 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
              (pure (((! w__6) : Bool)))) : Bool)
         then
           (do
             let w__7 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
             (pure (((6 ≥b w__7) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
        then
          (do
            let w__10 ← (( do readReg MDSELR_EL1 ) : SailM (BitVec 64) )
            let w__11 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
            (pure ((((6 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK w__10)) *i 16)) ≥b w__11) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__13 : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__20 ← (( do
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
              if (w__20 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__27 ← (( do
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
                                    let w__24 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__24) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__27 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__31 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__29 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__30 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__29) +++ (_get_MDCR_EL2_Type_TDA
                                    w__30)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__31 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__33 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__33 : Bool)
                          then
                            (do
                              let w__35 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__35 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__39 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__36 ← (( do readReg OSLSR_EL1 ) : SailM
                                             (BitVec 64) )
                                           (pure ((((_get_OSLSR_EL1_Type_OSLK w__36) == 0#1) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaltingAllowed ()))
                                      else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__39 : Bool)
                              then
                                (do
                                  (Halt DebugHalt_SoftwareAccess))
                              else
                                (do
                                  let w__40 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) :
                                    SailM Bool )
                                  if (w__40 : Bool)
                                  then
                                    (do
                                      let w__41 ← (( do readReg DBGWVR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__42 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                        (BitVec 2) )
                                      (X_set t 64
                                        (__get_DBGWVR_EL1
                                          (GetElem?.getElem! w__41
                                            (Sail.Int.toNatChecked ((6 +i ((BitVec.toNat w__42) *i 16))))))))
                                  else
                                    (do
                                      let w__43 ← (( do readReg DBGWVR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! w__43 6))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__50 ← (( do
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
                  if (w__50 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__52 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__52 : Bool)
                      then
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__54 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__55 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                       (pure ((((_get_OSLSR_EL1_Type_OSLK w__55) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__58 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__59 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM
                                Bool )
                              if (w__59 : Bool)
                              then
                                (do
                                  let w__60 ← (( do readReg DBGWVR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__61 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                    (BitVec 2) )
                                  (X_set t 64
                                    (__get_DBGWVR_EL1
                                      (GetElem?.getElem! w__60
                                        (Sail.Int.toNatChecked ((6 +i ((BitVec.toNat w__61) *i 16))))))))
                              else
                                (do
                                  let w__62 ← (( do readReg DBGWVR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! w__62 6))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__66 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__63 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                   (pure ((((_get_OSLSR_EL1_Type_OSLK w__63) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__66 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__67 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
                          if (w__67 : Bool)
                          then
                            (do
                              let w__68 ← (( do readReg DBGWVR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__69 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2)
                                )
                              (X_set t 64
                                (__get_DBGWVR_EL1
                                  (GetElem?.getElem! w__68
                                    (Sail.Int.toNatChecked ((6 +i ((BitVec.toNat w__69) *i 16))))))))
                          else
                            (do
                              let w__70 ← (( do readReg DBGWVR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! w__70 6))))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_5cfc3b8e8ae8a2a4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 w__4)
  let w__5 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__5)
  let w__13 ← (( do
    if ((← do
         if ((← do
              let w__6 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
              (pure (((! w__6) : Bool)))) : Bool)
         then
           (do
             let w__7 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
             (pure (((5 ≥b w__7) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
        then
          (do
            let w__10 ← (( do readReg MDSELR_EL1 ) : SailM (BitVec 64) )
            let w__11 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
            (pure ((((5 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK w__10)) *i 16)) ≥b w__11) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__13 : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__20 ← (( do
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
              if (w__20 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__27 ← (( do
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
                                    let w__24 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__24) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__27 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__31 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__29 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__30 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__29) +++ (_get_MDCR_EL2_Type_TDA
                                    w__30)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__31 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__33 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__33 : Bool)
                          then
                            (do
                              let w__35 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__35 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__39 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__36 ← (( do readReg OSLSR_EL1 ) : SailM
                                             (BitVec 64) )
                                           (pure ((((_get_OSLSR_EL1_Type_OSLK w__36) == 0#1) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaltingAllowed ()))
                                      else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__39 : Bool)
                              then
                                (do
                                  (Halt DebugHalt_SoftwareAccess))
                              else
                                (do
                                  let w__40 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) :
                                    SailM Bool )
                                  if (w__40 : Bool)
                                  then
                                    (do
                                      let w__41 ← (( do readReg DBGWVR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__42 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                        (BitVec 2) )
                                      (X_set t 64
                                        (__get_DBGWVR_EL1
                                          (GetElem?.getElem! w__41
                                            (Sail.Int.toNatChecked ((5 +i ((BitVec.toNat w__42) *i 16))))))))
                                  else
                                    (do
                                      let w__43 ← (( do readReg DBGWVR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! w__43 5))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__50 ← (( do
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
                  if (w__50 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__52 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__52 : Bool)
                      then
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__54 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__55 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                       (pure ((((_get_OSLSR_EL1_Type_OSLK w__55) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__58 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__59 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM
                                Bool )
                              if (w__59 : Bool)
                              then
                                (do
                                  let w__60 ← (( do readReg DBGWVR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__61 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                    (BitVec 2) )
                                  (X_set t 64
                                    (__get_DBGWVR_EL1
                                      (GetElem?.getElem! w__60
                                        (Sail.Int.toNatChecked ((5 +i ((BitVec.toNat w__61) *i 16))))))))
                              else
                                (do
                                  let w__62 ← (( do readReg DBGWVR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! w__62 5))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__66 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__63 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                   (pure ((((_get_OSLSR_EL1_Type_OSLK w__63) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__66 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__67 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
                          if (w__67 : Bool)
                          then
                            (do
                              let w__68 ← (( do readReg DBGWVR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__69 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2)
                                )
                              (X_set t 64
                                (__get_DBGWVR_EL1
                                  (GetElem?.getElem! w__68
                                    (Sail.Int.toNatChecked ((5 +i ((BitVec.toNat w__69) *i 16))))))))
                          else
                            (do
                              let w__70 ← (( do readReg DBGWVR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! w__70 5))))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGWVR_EL1_SysRegRead_695a90ac9c89a050 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_DBGWVRn_EL1 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_DBGWVRn_EL1 w__4)
  let w__5 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__5)
  let w__13 ← (( do
    if ((← do
         if ((← do
              let w__6 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
              (pure (((! w__6) : Bool)))) : Bool)
         then
           (do
             let w__7 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
             (pure (((1 ≥b w__7) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
        then
          (do
            let w__10 ← (( do readReg MDSELR_EL1 ) : SailM (BitVec 64) )
            let w__11 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
            (pure ((((1 +i ((BitVec.toNat (_get_MDSELR_EL1_Type_BANK w__10)) *i 16)) ≥b w__11) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__13 : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__20 ← (( do
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
              if (w__20 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__27 ← (( do
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
                                    let w__24 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__24) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGRTR_EL2_DBGWVRn_EL1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__27 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__31 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__29 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__30 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__29) +++ (_get_MDCR_EL2_Type_TDA
                                    w__30)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__31 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__33 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__33 : Bool)
                          then
                            (do
                              let w__35 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__35 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__39 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__36 ← (( do readReg OSLSR_EL1 ) : SailM
                                             (BitVec 64) )
                                           (pure ((((_get_OSLSR_EL1_Type_OSLK w__36) == 0#1) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaltingAllowed ()))
                                      else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__39 : Bool)
                              then
                                (do
                                  (Halt DebugHalt_SoftwareAccess))
                              else
                                (do
                                  let w__40 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) :
                                    SailM Bool )
                                  if (w__40 : Bool)
                                  then
                                    (do
                                      let w__41 ← (( do readReg DBGWVR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__42 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                        (BitVec 2) )
                                      (X_set t 64
                                        (__get_DBGWVR_EL1
                                          (GetElem?.getElem! w__41
                                            (Sail.Int.toNatChecked ((1 +i ((BitVec.toNat w__42) *i 16))))))))
                                  else
                                    (do
                                      let w__43 ← (( do readReg DBGWVR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! w__43 1))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__50 ← (( do
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
                  if (w__50 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__52 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__52 : Bool)
                      then
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__54 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__55 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                       (pure ((((_get_OSLSR_EL1_Type_OSLK w__55) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__58 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__59 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM
                                Bool )
                              if (w__59 : Bool)
                              then
                                (do
                                  let w__60 ← (( do readReg DBGWVR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__61 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                    (BitVec 2) )
                                  (X_set t 64
                                    (__get_DBGWVR_EL1
                                      (GetElem?.getElem! w__60
                                        (Sail.Int.toNatChecked ((1 +i ((BitVec.toNat w__61) *i 16))))))))
                              else
                                (do
                                  let w__62 ← (( do readReg DBGWVR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! w__62 1))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__66 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__63 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                   (pure ((((_get_OSLSR_EL1_Type_OSLK w__63) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__66 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__67 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
                          if (w__67 : Bool)
                          then
                            (do
                              let w__68 ← (( do readReg DBGWVR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__69 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2)
                                )
                              (X_set t 64
                                (__get_DBGWVR_EL1
                                  (GetElem?.getElem! w__68
                                    (Sail.Int.toNatChecked ((1 +i ((BitVec.toNat w__69) *i 16))))))))
                          else
                            (do
                              let w__70 ← (( do readReg DBGWVR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              (X_set t 64 (__get_DBGWVR_EL1 (GetElem?.getElem! w__70 1))))))
                  else (pure (()))))))


end ArmFull.Functions
