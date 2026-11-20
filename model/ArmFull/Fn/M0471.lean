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
public import ArmFull.Fn.M0072
public import ArmFull.Fn.M0080
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0112
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0251
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
def ELR_EL2_SysRegWrite_428ab6f83a3c959c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__11 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 if ((← do
                                      (IsFeatureImplemented FEAT_GCS)) : Bool)
                                 then
                                   (do
                                     (GetCurrentEXLOCKEN ()))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__5 ← (( do (Halted ()) ) : SailM Bool )
                                (pure (((! w__5) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__7.EXLOCK == 1#1) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      (EL2Enabled ()))
                  else (pure false)) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then
            (do
              (EXLOCKException ()))
          else
            (do
              let w__15 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__13) +++ (_get_HCR_EL2_Type_NV w__14)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__15 : Bool)
              then
                (do
                  let w__16 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg ELR_EL1 w__16)
              else
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else sailThrow ((Error_Undefined ())))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__25 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               (IsFeatureImplemented FEAT_GCS)) : Bool)
                          then
                            (do
                              (GetCurrentEXLOCKEN ()))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__22 ← (( do (Halted ()) ) : SailM Bool )
                         (pure (((! w__22) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__24.EXLOCK == 1#1) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__25 : Bool)
              then
                (do
                  (EXLOCKException ()))
              else
                (do
                  let w__26 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg ELR_EL2 w__26))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg ELR_EL2 w__27)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ELR_EL3_SysRegWrite_95989f8c3fc9cabc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EXLOCK : (BitVec 1) := w__1.EXLOCK
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
                  let w__7 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (IsFeatureImplemented FEAT_GCS)) : Bool)
                               then
                                 (do
                                   (GetCurrentEXLOCKEN ()))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__5 ← (( do (Halted ()) ) : SailM Bool )
                              (pure (((! w__5) : Bool))))
                          else (pure false)) && ((__PSTATE_EXLOCK == 1#1) : Bool))) ) : SailM Bool )
                  if (w__7 : Bool)
                  then
                    (do
                      (EXLOCKException ()))
                  else
                    (do
                      let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ELR_EL3 w__8))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ERRSELR_EL1_SysRegWrite_91762c9f88299554 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TERR : (BitVec 1) := (_get_SCR_EL3_Type_TERR w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TWERR : (BitVec 1) := (_get_SCR_EL3_Type_TWERR w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TERR : (BitVec 1) := (_get_HCR_EL2_Type_TERR w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__5)
  let w__6 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_ERRSELR_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_ERRSELR_EL1 w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__13 ← (( do
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
                  else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
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
                      else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__20 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__22 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__29 ← (( do
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
                                        let w__26 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__26) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HFGWTR_EL2_ERRSELR_EL1 == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__29 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__31 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__31 : Bool)
                          then
                            (do
                              let w__33 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__33 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__35 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__35 : Bool)
                              then
                                (do
                                  let w__37 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__37 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ERRSELR_EL1 (Mk_ERRSELR_EL1_Type w__38))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__45 ← (( do
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
                      else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__45 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__52 ← (( do
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
                          else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__52 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__54 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
                      if (w__54 : Bool)
                      then
                        (do
                          let w__56 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__56 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__58 : Bool)
                          then
                            (do
                              let w__60 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__60 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__61 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ERRSELR_EL1 (Mk_ERRSELR_EL1_Type w__61))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__62 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg ERRSELR_EL1 (Mk_ERRSELR_EL1_Type w__62))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ERXADDR_EL1_SysRegWrite_279c161c3f15ad75 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TERR : (BitVec 1) := (_get_SCR_EL3_Type_TERR w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TWERR : (BitVec 1) := (_get_SCR_EL3_Type_TWERR w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TERR : (BitVec 1) := (_get_HCR_EL2_Type_TERR w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__5)
  let w__6 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_ERXADDR_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_ERXADDR_EL1 w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__13 ← (( do
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
                  else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
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
                      else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__20 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__22 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__29 ← (( do
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
                                        let w__26 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__26) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HFGWTR_EL2_ERXADDR_EL1 == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__29 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__31 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__31 : Bool)
                          then
                            (do
                              let w__33 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__33 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__35 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__35 : Bool)
                              then
                                (do
                                  let w__37 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__37 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ERXADDR_EL1 w__38)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__45 ← (( do
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
                      else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__45 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__52 ← (( do
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
                          else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__52 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__54 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
                      if (w__54 : Bool)
                      then
                        (do
                          let w__56 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__56 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__58 : Bool)
                          then
                            (do
                              let w__60 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__60 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__61 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ERXADDR_EL1 w__61)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__62 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg ERXADDR_EL1 w__62)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ERXCTLR_EL1_SysRegWrite_906c95adeb6439bf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TERR : (BitVec 1) := (_get_SCR_EL3_Type_TERR w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TWERR : (BitVec 1) := (_get_SCR_EL3_Type_TWERR w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TERR : (BitVec 1) := (_get_HCR_EL2_Type_TERR w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__5)
  let w__6 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_ERXCTLR_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_ERXCTLR_EL1 w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__13 ← (( do
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
                  else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
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
                      else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__20 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__22 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__29 ← (( do
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
                                        let w__26 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__26) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HFGWTR_EL2_ERXCTLR_EL1 == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__29 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__31 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__31 : Bool)
                          then
                            (do
                              let w__33 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__33 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__35 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__35 : Bool)
                              then
                                (do
                                  let w__37 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__37 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ERXCTLR_EL1 w__38)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__45 ← (( do
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
                      else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__45 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__52 ← (( do
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
                          else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__52 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__54 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
                      if (w__54 : Bool)
                      then
                        (do
                          let w__56 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__56 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__58 : Bool)
                          then
                            (do
                              let w__60 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__60 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__61 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ERXCTLR_EL1 w__61)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__62 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg ERXCTLR_EL1 w__62)
              else (pure (())))))


end ArmFull.Functions
