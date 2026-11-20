module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0064
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
                                      let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg OSDTRRX_EL1 w__37)))))))
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
                                  let w__60 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg OSDTRRX_EL1 w__60)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__61 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg OSDTRRX_EL1 w__61)
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
                                      let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg OSDTRTX_EL1 w__37)))))))
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
                                  let w__60 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg OSDTRTX_EL1 w__60)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__61 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg OSDTRTX_EL1 w__61)
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def OSECCR_EL1_SysRegWrite_e6c17a3df51100b5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_OSECCR_EL1 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_OSECCR_EL1 w__4)
  let w__5 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  let __OSLSR_EL1_OSLK : (BitVec 1) := (_get_OSLSR_EL1_Type_OSLK w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
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
                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__19 ← (( do
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
                                let w__16 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__16) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HDFGWTR_EL2_OSECCR_EL1 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__19 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__23 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__21 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__22 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__21) +++ (_get_MDCR_EL2_Type_TDA w__22)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__25 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__25 : Bool)
                      then
                        (do
                          let w__27 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__27 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          if ((__OSLSR_EL1_OSLK == 0#1) : Bool)
                          then (pure (()))
                          else
                            (do
                              let w__28 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg OSECCR_EL1 (Mk_OSECCR_EL1_Type w__28)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__35 ← (( do
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
              if (w__35 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__37 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__37 : Bool)
                  then
                    (do
                      let w__39 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__39 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      if ((__OSLSR_EL1_OSLK == 0#1) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg OSECCR_EL1 (Mk_OSECCR_EL1_Type w__40)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__OSLSR_EL1_OSLK == 0#1) : Bool)
                  then (pure (()))
                  else
                    (do
                      let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg OSECCR_EL1 (Mk_OSECCR_EL1_Type w__41)))
              else (pure (())))))


end ArmFull.Functions
