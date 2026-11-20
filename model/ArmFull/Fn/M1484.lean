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
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0052
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0112
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0251
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0440
public import ArmFull.Fn.M0582
public import ArmFull.Fn.M0583
public import ArmFull.Fn.M0584
public import ArmFull.Fn.M0585
public import ArmFull.Fn.M1340
public import ArmFull.Fn.M1341
public import ArmFull.Fn.M1342 set_option backward.proofsInPublic true @[expose] public section

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
def ZCR_EL1_SysRegWrite_8900d1c129d0830f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  let w__4 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_EZ : (BitVec 1) := (_get_CPTR_EL3_Type_EZ w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_ZEN : (BitVec 2) := (_get_CPTR_EL2_Type_ZEN w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__7) +++ ((_get_HCR_EL2_Type_NV1 w__8) +++ (_get_HCR_EL2_Type_NV
                          w__9))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__10 : Bool)
          then
            (do
              let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x1E0#12) w__11))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
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
                          else (pure false)) && ((__CPTR_EL3_EZ == 0#1) : Bool))) ) : SailM Bool )
                  if (w__20 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((let b__0 := __CPTR_EL2_ZEN
                         (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                         then true
                         else false : Bool)) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8)))
                      else
                        (do
                          let w__22 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_EZ == 0#1) : Bool))) ) : SailM Bool
                            )
                          if (w__22 : Bool)
                          then
                            (do
                              let w__24 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__24 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8))))
                          else
                            (do
                              let w__25 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ZCR_EL1 (Mk_ZCR_EL1_Type w__25)))))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__27 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__27) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      if ((__CPTR_EL3_EZ == 0#1) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8)))
                      else
                        (do
                          let w__30 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ZCR_EL1 (Mk_ZCR_EL1_Type w__30)))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSPOPCX_SysOpsWrite_8b33b35a7177cc05 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EXLOCK : (BitVec 1) := w__1.EXLOCK
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_nGCSEPP : (BitVec 1) := (_get_HFGITR_EL2_Type_nGCSEPP w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
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
                      let w__7 ← (( do (Halted ()) ) : SailM Bool )
                      (pure (((! w__7) : Bool))))
                  else (pure false)) && ((__PSTATE_EXLOCK == 1#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (EXLOCKException ()))
          else
            (do
              let w__16 ← (( do
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
                                let w__13 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__13) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_nGCSEPP == 0#1) : Bool))) ) : SailM Bool
                )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (GCSPOPCX ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__22 ← (( do
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
                          let w__20 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__20) : Bool))))
                      else (pure false)) && ((__PSTATE_EXLOCK == 1#1) : Bool))) ) : SailM Bool )
              if (w__22 : Bool)
              then
                (do
                  (EXLOCKException ()))
              else
                (do
                  (GCSPOPCX ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__28 ← (( do
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
                              let w__26 ← (( do (Halted ()) ) : SailM Bool )
                              (pure (((! w__26) : Bool))))
                          else (pure false)) && ((__PSTATE_EXLOCK == 1#1) : Bool))) ) : SailM Bool )
                  if (w__28 : Bool)
                  then
                    (do
                      (EXLOCKException ()))
                  else
                    (do
                      (GCSPOPCX ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSPUSHM_SysOpsWrite_7d31b427953fb1be (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  let __GCSCRE0_EL1_PUSHMEn : (BitVec 1) := (_get_GCSCRE0_EL1_Type_PUSHMEn w__2)
  let w__3 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  let __GCSCR_EL1_PUSHMEn : (BitVec 1) := (_get_GCSCR_EL1_Type_PUSHMEn w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_nGCSPUSHM_EL1 : (BitVec 1) := (_get_HFGITR_EL2_Type_nGCSPUSHM_EL1 w__5)
  let w__6 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  let __GCSCR_EL2_PUSHMEn : (BitVec 1) := (_get_GCSCR_EL2_Type_PUSHMEn w__6)
  let w__7 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  let __GCSCR_EL3_PUSHMEn : (BitVec 1) := (_get_GCSCR_EL3_Type_PUSHMEn w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__10 ← (( do
        (pure ((← do
              (pure ((← do
                    let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                    (pure (((! w__8) : Bool)))) || ((__HCR_EL2_TGE != 1#1) : Bool)))) && ((__GCSCRE0_EL1_PUSHMEn == 0#1) : Bool)))
        ) : SailM Bool )
      if (w__10 : Bool)
      then
        (do
          (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          let w__13 ← (( do
            (pure ((← do
                  (pure ((← do
                        (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool)))) && ((__GCSCRE0_EL1_PUSHMEn == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (GCSPUSHM w__14))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((__GCSCR_EL1_PUSHMEn == 0#1) : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__21 ← (( do
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
                                let w__18 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__18) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_nGCSPUSHM_EL1 == 0#1) : Bool))) ) : SailM
                Bool )
              if (w__21 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__22 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (GCSPUSHM w__22))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__GCSCR_EL2_PUSHMEn == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__23 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (GCSPUSHM w__23)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__GCSCR_EL3_PUSHMEn == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__24 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (GCSPUSHM w__24)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSPUSHX_SysOpsWrite_c023a281d843c45a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EXLOCK : (BitVec 1) := w__1.EXLOCK
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_nGCSEPP : (BitVec 1) := (_get_HFGITR_EL2_Type_nGCSEPP w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
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
                      let w__7 ← (( do (Halted ()) ) : SailM Bool )
                      (pure (((! w__7) : Bool))))
                  else (pure false)) && ((__PSTATE_EXLOCK == 0#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (EXLOCKException ()))
          else
            (do
              let w__16 ← (( do
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
                                let w__13 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__13) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_nGCSEPP == 0#1) : Bool))) ) : SailM Bool
                )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (GCSPUSHX ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__22 ← (( do
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
                          let w__20 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__20) : Bool))))
                      else (pure false)) && ((__PSTATE_EXLOCK == 0#1) : Bool))) ) : SailM Bool )
              if (w__22 : Bool)
              then
                (do
                  (EXLOCKException ()))
              else
                (do
                  (GCSPUSHX ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__28 ← (( do
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
                              let w__26 ← (( do (Halted ()) ) : SailM Bool )
                              (pure (((! w__26) : Bool))))
                          else (pure false)) && ((__PSTATE_EXLOCK == 0#1) : Bool))) ) : SailM Bool )
                  if (w__28 : Bool)
                  then
                    (do
                      (EXLOCKException ()))
                  else
                    (do
                      (GCSPUSHX ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AArch64_AutoGen_SysInstrWithResult (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((((((CRm == 0b0111#4) && (CRn == 0b0111#4)) && (op0 == 0b01#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
  then
    (do
      (GCSSS2_SysInstrWithResult_f9ffdfaa333b34bf el op0 op1 CRn op2 CRm t))
  else
    (do
      if ((((((CRm == 0b0111#4) && (CRn == 0b0111#4)) && (op0 == 0b01#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
      then
        (do
          (GCSPOPM_SysInstrWithResult_785f34ad5cd557fe el op0 op1 CRn op2 CRm t))
      else
        (do
          (AArch64_UnallocatedSysRegAccess op0 op1 CRn op2 CRm false t)))


/-- Type quantifiers: t : Int, t2 : Int -/
def AArch64_AutoGen_SysRegRead128 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  if ((((((CRm == 0b0100#4) && (CRn == 0b0111#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
  then
    (do
      (PAR_EL1_SysRegRead128_8206ac7c9b0eef57 el op0 op1 CRn op2 CRm t t2))
  else
    (do
      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
      then
        (do
          (RCWSMASK_EL1_SysRegRead128_7cac5e35b1fae5f9 el op0 op1 CRn op2 CRm t t2))
      else
        (do
          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
          then
            (do
              (TTBR1_EL2_SysRegRead128_ae708511fcb38e92 el op0 op1 CRn op2 CRm t t2))
          else
            (do
              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
              then
                (do
                  (TTBR1_EL1_SysRegRead128_16388106e031d578 el op0 op1 CRn op2 CRm t t2))
              else
                (do
                  if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                  then
                    (do
                      (TTBR0_EL2_SysRegRead128_05dc18b820cc86b7 el op0 op1 CRn op2 CRm t t2))
                  else
                    (do
                      if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                      then
                        (do
                          (TTBR0_EL1_SysRegRead128_e74a87d5451e7769 el op0 op1 CRn op2 CRm t t2))
                      else
                        (do
                          if ((((((CRm == 0b0001#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                          then
                            (do
                              (VTTBR_EL2_SysRegRead128_a9b3226c12a0e07e el op0 op1 CRn op2 CRm t t2))
                          else
                            (do
                              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                              then
                                (do
                                  (TTBR0_EL1_SysRegRead128_ef7a13f49fb9674d el op0 op1 CRn op2 CRm t
                                    t2))
                              else
                                (do
                                  if ((((((match CRm with
                                             | b__0 => true : Bool) && (let b__1 := CRn
                                             (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                      b__1 3 3)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                      b__1 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                                             then true
                                             else false : Bool))) && (op0 == 0b11#2)) && (match op1 with
                                         | b__2 => true : Bool)) && (match op2 with
                                       | b__3 => true : Bool)) : Bool)
                                  then
                                    (do
                                      (S3_op1_Cn_Cm_op2_SysRegRead128_6403c05d5d1898d5 el op0 op1
                                        CRn op2 CRm t t2))
                                  else
                                    (do
                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                      then
                                        (do
                                          (RCWMASK_EL1_SysRegRead128_7c7466f3a5148cfe el op0 op1 CRn
                                            op2 CRm t t2))
                                      else
                                        (do
                                          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                          then
                                            (do
                                              (TTBR1_EL2_SysRegRead128_712360e50061655a el op0 op1
                                                CRn op2 CRm t t2))
                                          else
                                            (do
                                              (AArch64_UnallocatedSysRegAccess op0 op1 CRn op2 CRm
                                                true t))))))))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AArch64_AutoGen_SysRegWrite128 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  if ((((((CRm == 0b0100#4) && (CRn == 0b0111#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
  then
    (do
      (PAR_EL1_SysRegWrite128_e67f3244d494abe6 el op0 op1 CRn op2 CRm t t2))
  else
    (do
      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
      then
        (do
          (RCWSMASK_EL1_SysRegWrite128_d70b97b0479af313 el op0 op1 CRn op2 CRm t t2))
      else
        (do
          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
          then
            (do
              (TTBR1_EL2_SysRegWrite128_4bfd1913f2c26b7d el op0 op1 CRn op2 CRm t t2))
          else
            (do
              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
              then
                (do
                  (TTBR1_EL1_SysRegWrite128_d20c29029eb4ed94 el op0 op1 CRn op2 CRm t t2))
              else
                (do
                  if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                  then
                    (do
                      (TTBR0_EL2_SysRegWrite128_db720477dd35bd78 el op0 op1 CRn op2 CRm t t2))
                  else
                    (do
                      if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                      then
                        (do
                          (TTBR0_EL1_SysRegWrite128_66ee61de597f133e el op0 op1 CRn op2 CRm t t2))
                      else
                        (do
                          if ((((((CRm == 0b0001#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                          then
                            (do
                              (VTTBR_EL2_SysRegWrite128_3ec09d9d33270957 el op0 op1 CRn op2 CRm t t2))
                          else
                            (do
                              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                              then
                                (do
                                  (TTBR0_EL1_SysRegWrite128_8ea27f288a4b152e el op0 op1 CRn op2 CRm
                                    t t2))
                              else
                                (do
                                  if ((((((match CRm with
                                             | b__0 => true : Bool) && (let b__1 := CRn
                                             (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                      b__1 3 3)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                      b__1 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                                             then true
                                             else false : Bool))) && (op0 == 0b11#2)) && (match op1 with
                                         | b__2 => true : Bool)) && (match op2 with
                                       | b__3 => true : Bool)) : Bool)
                                  then
                                    (do
                                      (S3_op1_Cn_Cm_op2_SysRegWrite128_54572e14feed5fe8 el op0 op1
                                        CRn op2 CRm t t2))
                                  else
                                    (do
                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                      then
                                        (do
                                          (RCWMASK_EL1_SysRegWrite128_b8a59eaf95f35a5f el op0 op1
                                            CRn op2 CRm t t2))
                                      else
                                        (do
                                          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                          then
                                            (do
                                              (TTBR1_EL2_SysRegWrite128_c87556637100112b el op0 op1
                                                CRn op2 CRm t t2))
                                          else
                                            (do
                                              (AArch64_UnallocatedSysRegAccess op0 op1 CRn op2 CRm
                                                false t))))))))))))


end ArmFull.Functions
