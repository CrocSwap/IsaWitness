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
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M1340 set_option backward.proofsInPublic true @[expose] public section

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
def PMBPTR_EL1_SysRegWrite_2410b0966d5ddbf7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_NSPBE : (BitVec 1) := (_get_MDCR_EL3_Type_NSPBE w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NSE : (BitVec 1) := (_get_SCR_EL3_Type_NSE w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMBPTR_EL1 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMBPTR_EL1 w__4)
  let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_E2PB : (BitVec 2) := (_get_MDCR_EL2_Type_E2PB w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__20 ← (( do
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
                          let w__9 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                          (pure ((((_get_EDSCR_Type_SDD w__9) == 1#1) : Bool))))
                      else (pure false)) : Bool)
                 then
                   (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                 else (pure false)) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          let w__13 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                          (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                  (_get_MDCR_EL3_Type_NSPB w__13) 0)])) == 0#1) : Bool)))) : Bool)
                     then (pure true)
                     else
                       (do
                         let w__14 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                         let w__15 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 (_get_MDCR_EL3_Type_NSPB w__14) 1)])) != (_get_SCR_EL3_Type_NS
                               w__15)) : Bool))))) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
            else (pure false) ) : SailM Bool )
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
                      else (pure false)) && ((__HDFGWTR_EL2_PMBPTR_EL1 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__27 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && (let b__0 := __MDCR_EL2_E2PB
                        (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                        then true
                        else false : Bool)))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__38 ← (( do
                        if ((← do
                             (HaveEL EL3)) : Bool)
                        then
                          (do
                            if ((← do
                                 if ((← do
                                      let w__31 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                      (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                              (_get_MDCR_EL3_Type_NSPB w__31) 0)])) == 0#1) : Bool)))) : Bool)
                                 then (pure true)
                                 else
                                   (do
                                     let w__32 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                     let w__33 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                     (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             (_get_MDCR_EL3_Type_NSPB w__32) 1)])) != (_get_SCR_EL3_Type_NS
                                           w__33)) : Bool))))) : Bool)
                            then (pure true)
                            else
                              (do
                                (pure ((← do
                                      (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__38 : Bool)
                      then
                        (do
                          let w__41 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__40 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__40) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__41 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__45 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_NV2 w__43) +++ (_get_HCR_EL2_Type_NV
                                        w__44)) == 0b11#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__45 : Bool)
                          then
                            (do
                              let w__46 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (NVMem_set (BitVec.toNat 0x810#12) w__46))
                          else
                            (do
                              let w__47 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg PMBPTR_EL1 (Mk_PMBPTR_EL1_Type w__47)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__62 ← (( do
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
                              let w__51 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                              (pure ((((_get_EDSCR_Type_SDD w__51) == 1#1) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                     else (pure false)) : Bool)
                then
                  (do
                    if ((← do
                         if ((← do
                              let w__55 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                              (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                      (_get_MDCR_EL3_Type_NSPB w__55) 0)])) == 0#1) : Bool)))) : Bool)
                         then (pure true)
                         else
                           (do
                             let w__56 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                             let w__57 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     (_get_MDCR_EL3_Type_NSPB w__56) 1)])) != (_get_SCR_EL3_Type_NS
                                   w__57)) : Bool))))) : Bool)
                    then (pure true)
                    else
                      (do
                        (pure ((← do
                              (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                else (pure false) ) : SailM Bool )
              if (w__62 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__71 ← (( do
                    if ((← do
                         (HaveEL EL3)) : Bool)
                    then
                      (do
                        if ((← do
                             if ((← do
                                  let w__64 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                  (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                          (_get_MDCR_EL3_Type_NSPB w__64) 0)])) == 0#1) : Bool)))) : Bool)
                             then (pure true)
                             else
                               (do
                                 let w__65 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                 let w__66 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         (_get_MDCR_EL3_Type_NSPB w__65) 1)])) != (_get_SCR_EL3_Type_NS
                                       w__66)) : Bool))))) : Bool)
                        then (pure true)
                        else
                          (do
                            (pure ((← do
                                  (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                    else (pure false) ) : SailM Bool )
                  if (w__71 : Bool)
                  then
                    (do
                      let w__74 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__73 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__73) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__74 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__75 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg PMBPTR_EL1 (Mk_PMBPTR_EL1_Type w__75))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__76 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PMBPTR_EL1 (Mk_PMBPTR_EL1_Type w__76))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PMBSR_EL1_SysRegWrite_0ff3921bb4e54efe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_NSPBE : (BitVec 1) := (_get_MDCR_EL3_Type_NSPBE w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NSE : (BitVec 1) := (_get_SCR_EL3_Type_NSE w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMBSR_EL1 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMBSR_EL1 w__4)
  let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_E2PB : (BitVec 2) := (_get_MDCR_EL2_Type_E2PB w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__20 ← (( do
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
                          let w__9 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                          (pure ((((_get_EDSCR_Type_SDD w__9) == 1#1) : Bool))))
                      else (pure false)) : Bool)
                 then
                   (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                 else (pure false)) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          let w__13 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                          (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                  (_get_MDCR_EL3_Type_NSPB w__13) 0)])) == 0#1) : Bool)))) : Bool)
                     then (pure true)
                     else
                       (do
                         let w__14 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                         let w__15 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 (_get_MDCR_EL3_Type_NSPB w__14) 1)])) != (_get_SCR_EL3_Type_NS
                               w__15)) : Bool))))) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
            else (pure false) ) : SailM Bool )
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
                      else (pure false)) && ((__HDFGWTR_EL2_PMBSR_EL1 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__27 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && (let b__0 := __MDCR_EL2_E2PB
                        (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                        then true
                        else false : Bool)))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__38 ← (( do
                        if ((← do
                             (HaveEL EL3)) : Bool)
                        then
                          (do
                            if ((← do
                                 if ((← do
                                      let w__31 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                      (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                              (_get_MDCR_EL3_Type_NSPB w__31) 0)])) == 0#1) : Bool)))) : Bool)
                                 then (pure true)
                                 else
                                   (do
                                     let w__32 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                     let w__33 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                     (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             (_get_MDCR_EL3_Type_NSPB w__32) 1)])) != (_get_SCR_EL3_Type_NS
                                           w__33)) : Bool))))) : Bool)
                            then (pure true)
                            else
                              (do
                                (pure ((← do
                                      (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__38 : Bool)
                      then
                        (do
                          let w__41 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__40 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__40) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__41 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__45 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_NV2 w__43) +++ (_get_HCR_EL2_Type_NV
                                        w__44)) == 0b11#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__45 : Bool)
                          then
                            (do
                              let w__46 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (NVMem_set (BitVec.toNat 0x820#12) w__46))
                          else
                            (do
                              let w__47 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg PMBSR_EL1 (Mk_PMBSR_EL1_Type w__47)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__62 ← (( do
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
                              let w__51 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                              (pure ((((_get_EDSCR_Type_SDD w__51) == 1#1) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                     else (pure false)) : Bool)
                then
                  (do
                    if ((← do
                         if ((← do
                              let w__55 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                              (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                      (_get_MDCR_EL3_Type_NSPB w__55) 0)])) == 0#1) : Bool)))) : Bool)
                         then (pure true)
                         else
                           (do
                             let w__56 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                             let w__57 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     (_get_MDCR_EL3_Type_NSPB w__56) 1)])) != (_get_SCR_EL3_Type_NS
                                   w__57)) : Bool))))) : Bool)
                    then (pure true)
                    else
                      (do
                        (pure ((← do
                              (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                else (pure false) ) : SailM Bool )
              if (w__62 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__71 ← (( do
                    if ((← do
                         (HaveEL EL3)) : Bool)
                    then
                      (do
                        if ((← do
                             if ((← do
                                  let w__64 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                  (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                          (_get_MDCR_EL3_Type_NSPB w__64) 0)])) == 0#1) : Bool)))) : Bool)
                             then (pure true)
                             else
                               (do
                                 let w__65 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                 let w__66 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         (_get_MDCR_EL3_Type_NSPB w__65) 1)])) != (_get_SCR_EL3_Type_NS
                                       w__66)) : Bool))))) : Bool)
                        then (pure true)
                        else
                          (do
                            (pure ((← do
                                  (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                    else (pure false) ) : SailM Bool )
                  if (w__71 : Bool)
                  then
                    (do
                      let w__74 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__73 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__73) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__74 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__75 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg PMBSR_EL1 (Mk_PMBSR_EL1_Type w__75))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__76 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PMBSR_EL1 (Mk_PMBSR_EL1_Type w__76))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PMSCR_EL1_SysRegWrite_fdb38cc2774305af (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_NSPBE : (BitVec 1) := (_get_MDCR_EL3_Type_NSPBE w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NSE : (BitVec 1) := (_get_SCR_EL3_Type_NSE w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__6) +++ ((_get_HCR_EL2_Type_NV1 w__7) +++ (_get_HCR_EL2_Type_NV
                          w__8))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x828#12) w__10))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
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
                  let w__27 ← (( do
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
                        if ((← do
                             if ((← do
                                  let w__20 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                  (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                          (_get_MDCR_EL3_Type_NSPB w__20) 0)])) == 0#1) : Bool)))) : Bool)
                             then (pure true)
                             else
                               (do
                                 let w__21 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                 let w__22 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         (_get_MDCR_EL3_Type_NSPB w__21) 1)])) != (_get_SCR_EL3_Type_NS
                                       w__22)) : Bool))))) : Bool)
                        then (pure true)
                        else
                          (do
                            (pure ((← do
                                  (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                    else (pure false) ) : SailM Bool )
                  if (w__27 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__36 ← (( do
                        if ((← do
                             (HaveEL EL3)) : Bool)
                        then
                          (do
                            if ((← do
                                 if ((← do
                                      let w__29 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                      (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                              (_get_MDCR_EL3_Type_NSPB w__29) 0)])) == 0#1) : Bool)))) : Bool)
                                 then (pure true)
                                 else
                                   (do
                                     let w__30 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                     let w__31 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                     (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             (_get_MDCR_EL3_Type_NSPB w__30) 1)])) != (_get_SCR_EL3_Type_NS
                                           w__31)) : Bool))))) : Bool)
                            then (pure true)
                            else
                              (do
                                (pure ((← do
                                      (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__36 : Bool)
                      then
                        (do
                          let w__39 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__38 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__38) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__39 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg PMSCR_EL1 (Mk_PMSCR_EL1_Type w__40))))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__42 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__42) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__44 : Bool)
                  then
                    (do
                      let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg PMSCR_EL1 (Mk_PMSCR_EL1_Type w__45))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


end ArmFull.Functions
