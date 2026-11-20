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
public import ArmFull.Fn.M0074
public import ArmFull.Fn.M0075
public import ArmFull.Fn.M0076
public import ArmFull.Fn.M0079
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
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
def LORC_EL1_SysRegWrite_266317162c3d113d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TLOR : (BitVec 1) := (_get_SCR_EL3_Type_TLOR w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TLOR : (BitVec 1) := (_get_HCR_EL2_Type_TLOR w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__5)
  let w__6 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_LORC_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_LORC_EL1 w__6)
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
                  else (pure false)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__15 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TLOR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__15 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__22 ← (( do
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
                                        let w__19 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__19) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HFGWTR_EL2_LORC_EL1 == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__24 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__24 : Bool)
                          then
                            (do
                              let w__26 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__26 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg LORC_EL1 (Mk_LORC_EL1_Type w__27)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
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
                          else (pure false)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__34 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool )
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
                          let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg LORC_EL1 (Mk_LORC_EL1_Type w__39)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg LORC_EL1 (Mk_LORC_EL1_Type w__40)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def LOREA_EL1_SysRegWrite_12823f1415052a0d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TLOR : (BitVec 1) := (_get_SCR_EL3_Type_TLOR w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TLOR : (BitVec 1) := (_get_HCR_EL2_Type_TLOR w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__5)
  let w__6 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_LOREA_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_LOREA_EL1 w__6)
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
                  else (pure false)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__15 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TLOR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__15 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__22 ← (( do
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
                                        let w__19 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__19) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HFGWTR_EL2_LOREA_EL1 == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__24 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__24 : Bool)
                          then
                            (do
                              let w__26 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__26 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg LOREA_EL1 (Mk_LOREA_EL1_Type w__27)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
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
                          else (pure false)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__34 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool )
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
                          let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg LOREA_EL1 (Mk_LOREA_EL1_Type w__39)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg LOREA_EL1 (Mk_LOREA_EL1_Type w__40)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def LORN_EL1_SysRegWrite_8a9df4ed50885fe4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TLOR : (BitVec 1) := (_get_SCR_EL3_Type_TLOR w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TLOR : (BitVec 1) := (_get_HCR_EL2_Type_TLOR w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__5)
  let w__6 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_LORN_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_LORN_EL1 w__6)
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
                  else (pure false)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__15 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TLOR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__15 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__22 ← (( do
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
                                        let w__19 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__19) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HFGWTR_EL2_LORN_EL1 == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__24 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__24 : Bool)
                          then
                            (do
                              let w__26 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__26 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg LORN_EL1 (Mk_LORN_EL1_Type w__27)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
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
                          else (pure false)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__34 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool )
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
                          let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg LORN_EL1 (Mk_LORN_EL1_Type w__39)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg LORN_EL1 (Mk_LORN_EL1_Type w__40)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def LORSA_EL1_SysRegWrite_8563a4250c047bc4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TLOR : (BitVec 1) := (_get_SCR_EL3_Type_TLOR w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TLOR : (BitVec 1) := (_get_HCR_EL2_Type_TLOR w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__5)
  let w__6 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_LORSA_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_LORSA_EL1 w__6)
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
                  else (pure false)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__15 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TLOR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__15 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__22 ← (( do
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
                                        let w__19 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__19) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HFGWTR_EL2_LORSA_EL1 == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__24 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__24 : Bool)
                          then
                            (do
                              let w__26 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__26 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg LORSA_EL1 (Mk_LORSA_EL1_Type w__27)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__SCR_EL3_NS == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
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
                          else (pure false)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__34 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_TLOR == 1#1) : Bool))) ) : SailM Bool )
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
                          let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg LORSA_EL1 (Mk_LORSA_EL1_Type w__39)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg LORSA_EL1 (Mk_LORSA_EL1_Type w__40)))
              else (pure (())))))


end ArmFull.Functions
