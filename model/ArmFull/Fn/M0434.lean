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
public import ArmFull.Fn.M0069
public import ArmFull.Fn.M0074
public import ArmFull.Fn.M0076
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0132
public import ArmFull.Fn.M0135
public import ArmFull.Fn.M0142
public import ArmFull.Fn.M0144
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
def SPMIIDR_EL1_SysRegRead_895b44f480e2fb64 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_EnPM2 : (BitVec 1) := (_get_MDCR_EL3_Type_EnPM2 w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__2)
  let w__3 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR2_EL2_nSPMID : (BitVec 1) := (_get_HDFGRTR2_EL2_Type_nSPMID w__3)
  let w__4 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_EnSPM : (BitVec 1) := (_get_MDCR_EL2_Type_EnSPM w__4)
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
                       if ((← do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                (HaveEL EL3))
                            else (pure false)) : Bool)
                       then
                         (do
                           let w__8 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                           (pure ((((_get_EDSCR_Type_SDD w__8) == 1#1) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__21 ← (( do
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
                              let w__16 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                              (pure ((((_get_EDSCR_Type_SDD w__16) == 1#1) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__20 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                      (BitVec 2) )
                    (pure (((w__20 == 0b00#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__21 : Bool)
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
                                   (IsFeatureImplemented FEAT_FGT2))
                               else (pure false)) : Bool)
                          then
                            (do
                              (HaveEL EL3))
                          else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__27 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__31 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (IsFeatureImplemented FEAT_FGT2))
                              else (pure false)) && ((__HDFGRTR2_EL2_nSPMID == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__31 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__33 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__33 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__36 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__35 ← (( do (__get_selected_SPMACCESSR_EL2_field ()) ) :
                                      SailM (BitVec 2) )
                                    (pure (((w__35 == 0b00#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__36 : Bool)
                              then
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  let w__38 ← (( do
                                    (pure ((← do
                                          (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__38 : Bool)
                                  then
                                    (do
                                      let w__41 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__40 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__40) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__41 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                  else
                                    (do
                                      let w__44 ← (( do
                                        if ((← do
                                             (HaveEL EL3)) : Bool)
                                        then
                                          (do
                                            let w__43 ← (( do
                                              (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                                              (BitVec 2) )
                                            (pure (((w__43 == 0b00#2) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__44 : Bool)
                                      then
                                        (do
                                          let w__47 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__46 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__46) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__47 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                      else
                                        (do
                                          let w__48 ← (( do readReg SPMSELR_EL0 ) : SailM
                                            (BitVec 64) )
                                          (X_set t 64
                                            (SPMIIDR_EL1_read
                                              (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__48)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__56 ← (( do
                (pure ((← do
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
                               let w__52 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                               (pure ((((_get_EDSCR_Type_SDD w__52) == 1#1) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__56 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__65 ← (( do
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
                                  let w__60 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                  (pure ((((_get_EDSCR_Type_SDD w__60) == 1#1) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__64 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                          (BitVec 2) )
                        (pure (((w__64 == 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__65 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__67 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
                      if (w__67 : Bool)
                      then
                        (do
                          let w__70 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__69 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__69) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__70 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__73 ← (( do
                            if ((← do
                                 (HaveEL EL3)) : Bool)
                            then
                              (do
                                let w__72 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) :
                                  SailM (BitVec 2) )
                                (pure (((w__72 == 0b00#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__73 : Bool)
                          then
                            (do
                              let w__76 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__75 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__75) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__76 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__77 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              (X_set t 64
                                (SPMIIDR_EL1_read
                                  (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__77)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__78 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64
                    (SPMIIDR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__78)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPMINTENCLR_EL1_SysRegRead_6d6d9e36e779f16f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_EnPM2 : (BitVec 1) := (_get_MDCR_EL3_Type_EnPM2 w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__2)
  let w__3 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR2_EL2_nSPMINTEN : (BitVec 1) := (_get_HDFGRTR2_EL2_Type_nSPMINTEN w__3)
  let w__4 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_EnSPM : (BitVec 1) := (_get_MDCR_EL2_Type_EnSPM w__4)
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
                       if ((← do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                (HaveEL EL3))
                            else (pure false)) : Bool)
                       then
                         (do
                           let w__8 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                           (pure ((((_get_EDSCR_Type_SDD w__8) == 1#1) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__21 ← (( do
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
                              let w__16 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                              (pure ((((_get_EDSCR_Type_SDD w__16) == 1#1) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__20 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                      (BitVec 2) )
                    (pure (((w__20 == 0b00#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__21 : Bool)
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
                                   (IsFeatureImplemented FEAT_FGT2))
                               else (pure false)) : Bool)
                          then
                            (do
                              (HaveEL EL3))
                          else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__27 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__31 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (IsFeatureImplemented FEAT_FGT2))
                              else (pure false)) && ((__HDFGRTR2_EL2_nSPMINTEN == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__31 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__33 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__33 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__36 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__35 ← (( do (__get_selected_SPMACCESSR_EL2_field ()) ) :
                                      SailM (BitVec 2) )
                                    (pure (((w__35 == 0b00#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__36 : Bool)
                              then
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                              else
                                (do
                                  let w__38 ← (( do
                                    (pure ((← do
                                          (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__38 : Bool)
                                  then
                                    (do
                                      let w__41 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__40 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__40) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__41 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                  else
                                    (do
                                      let w__44 ← (( do
                                        if ((← do
                                             (HaveEL EL3)) : Bool)
                                        then
                                          (do
                                            let w__43 ← (( do
                                              (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                                              (BitVec 2) )
                                            (pure (((w__43 == 0b00#2) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__44 : Bool)
                                      then
                                        (do
                                          let w__47 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__46 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__46) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__47 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                      else
                                        (do
                                          let w__48 ← (( do readReg SPMSELR_EL0 ) : SailM
                                            (BitVec 64) )
                                          (X_set t 64
                                            (SPMINTENCLR_EL1_read
                                              (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__48)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__56 ← (( do
                (pure ((← do
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
                               let w__52 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                               (pure ((((_get_EDSCR_Type_SDD w__52) == 1#1) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__56 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__65 ← (( do
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
                                  let w__60 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                  (pure ((((_get_EDSCR_Type_SDD w__60) == 1#1) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__64 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) : SailM
                          (BitVec 2) )
                        (pure (((w__64 == 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__65 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__67 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
                      if (w__67 : Bool)
                      then
                        (do
                          let w__70 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__69 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__69) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__70 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__73 ← (( do
                            if ((← do
                                 (HaveEL EL3)) : Bool)
                            then
                              (do
                                let w__72 ← (( do (__get_selected_SPMACCESSR_EL3_field ()) ) :
                                  SailM (BitVec 2) )
                                (pure (((w__72 == 0b00#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__73 : Bool)
                          then
                            (do
                              let w__76 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__75 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__75) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__76 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__77 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              (X_set t 64
                                (SPMINTENCLR_EL1_read
                                  (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__77)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__78 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64
                    (SPMINTENCLR_EL1_read (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__78)))))
              else (pure (())))))


end ArmFull.Functions
