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
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0061
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0067
public import ArmFull.Fn.M0071
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
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
def PMSELR_EL0_SysRegWrite_e127f02e29e8e39d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TPM : (BitVec 1) := (_get_MDCR_EL3_Type_TPM w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMSELR_EL0 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMSELR_EL0 w__5)
  let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__6)
  if ((__PSTATE_EL == EL0) : Bool)
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
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__23 ← (( do
            if ((← do
                 if ((← do
                      (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                 then
                   (do
                     let w__15 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     let w__16 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     let w__17 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     (pure (((((_get_PMUSERENR_EL0_Type_UEN w__15) +++ ((_get_PMUSERENR_EL0_Type_ER
                               w__16) +++ (_get_PMUSERENR_EL0_Type_EN w__17))) == 0b000#3) : Bool))))
                 else (pure false)) : Bool)
            then (pure true)
            else
              (do
                if ((← do
                     let w__19 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                     (pure (((! w__19) : Bool)))) : Bool)
                then
                  (do
                    let w__20 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                    let w__21 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                    (pure (((((_get_PMUSERENR_EL0_Type_ER w__20) +++ (_get_PMUSERENR_EL0_Type_EN
                            w__21)) == 0b00#2) : Bool))))
                else (pure false)) ) : SailM Bool )
          if (w__23 : Bool)
          then
            (do
              let w__25 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__25 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__35 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__27) +++ (_get_HCR_EL2_Type_TGE
                                            w__28)) != 0b11#2) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT))
                           else (pure false)) : Bool)
                      then
                        (do
                          (pure ((← do
                                let w__32 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__32) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HDFGWTR_EL2_PMSELR_EL0 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__35 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__37 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__37 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__39 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__39 : Bool)
                      then
                        (do
                          let w__41 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__41 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg PMSELR_EL0 (Mk_PMSELR_EL0_Type w__42)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__49 ← (( do
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
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__49 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__56 ← (( do
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
                                let w__53 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__53) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HDFGWTR_EL2_PMSELR_EL0 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__56 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__58 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__58 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__60 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__60 : Bool)
                      then
                        (do
                          let w__62 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__62 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__63 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg PMSELR_EL0 (Mk_PMSELR_EL0_Type w__63))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__70 ← (( do
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
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__70 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__72 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__72 : Bool)
                  then
                    (do
                      let w__74 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__74 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__75 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg PMSELR_EL0 (Mk_PMSELR_EL0_Type w__75))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__76 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PMSELR_EL0 (Mk_PMSELR_EL0_Type w__76))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PMSFCR_EL1_SysRegWrite_a5237420ae2ed681 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_NSPBE : (BitVec 1) := (_get_MDCR_EL3_Type_NSPBE w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NSE : (BitVec 1) := (_get_SCR_EL3_Type_NSE w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMSFCR_EL1 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMSFCR_EL1 w__4)
  let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPMS : (BitVec 1) := (_get_MDCR_EL2_Type_TPMS w__5)
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
                      else (pure false)) && ((__HDFGWTR_EL2_PMSFCR_EL1 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__27 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__MDCR_EL2_TPMS == 1#1) : Bool))) ) : SailM Bool )
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
                          let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg PMSFCR_EL1 (Mk_PMSFCR_EL1_Type w__42))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__57 ← (( do
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
                              let w__46 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                              (pure ((((_get_EDSCR_Type_SDD w__46) == 1#1) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                     else (pure false)) : Bool)
                then
                  (do
                    if ((← do
                         if ((← do
                              let w__50 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                              (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                      (_get_MDCR_EL3_Type_NSPB w__50) 0)])) == 0#1) : Bool)))) : Bool)
                         then (pure true)
                         else
                           (do
                             let w__51 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                             let w__52 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     (_get_MDCR_EL3_Type_NSPB w__51) 1)])) != (_get_SCR_EL3_Type_NS
                                   w__52)) : Bool))))) : Bool)
                    then (pure true)
                    else
                      (do
                        (pure ((← do
                              (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                else (pure false) ) : SailM Bool )
              if (w__57 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__66 ← (( do
                    if ((← do
                         (HaveEL EL3)) : Bool)
                    then
                      (do
                        if ((← do
                             if ((← do
                                  let w__59 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                  (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                          (_get_MDCR_EL3_Type_NSPB w__59) 0)])) == 0#1) : Bool)))) : Bool)
                             then (pure true)
                             else
                               (do
                                 let w__60 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                 let w__61 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         (_get_MDCR_EL3_Type_NSPB w__60) 1)])) != (_get_SCR_EL3_Type_NS
                                       w__61)) : Bool))))) : Bool)
                        then (pure true)
                        else
                          (do
                            (pure ((← do
                                  (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                    else (pure false) ) : SailM Bool )
                  if (w__66 : Bool)
                  then
                    (do
                      let w__69 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__68 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__68) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__69 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__70 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg PMSFCR_EL1 (Mk_PMSFCR_EL1_Type w__70))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__71 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PMSFCR_EL1 (Mk_PMSFCR_EL1_Type w__71))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PMSSCR_EL1_SysRegWrite_13422cd11e2f6998 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_EnPMSS : (BitVec 1) := (_get_MDCR_EL3_Type_EnPMSS w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__3)
  let w__4 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR2_EL2_nPMSSCR_EL1 : (BitVec 1) := (_get_HDFGWTR2_EL2_Type_nPMSSCR_EL1 w__4)
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
                  else (pure false)) && ((__MDCR_EL3_EnPMSS == 0#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__17 ← (( do
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
                      else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__21 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HDFGWTR2_EL2_nPMSSCR_EL1 == 0#1) : Bool))) ) :
                    SailM Bool )
                  if (w__21 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__23 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_EnPMSS == 0#1) : Bool))) ) : SailM Bool
                        )
                      if (w__23 : Bool)
                      then
                        (do
                          let w__25 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__25 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__26 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (__set_PMSSCR_EL1 (Mk_PMSSCR_EL1_Type w__26)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__33 ← (( do
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
                      else (pure false)) && ((__MDCR_EL3_EnPMSS == 0#1) : Bool))) ) : SailM Bool )
              if (w__33 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__35 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_EnPMSS == 0#1) : Bool))) ) : SailM Bool )
                  if (w__35 : Bool)
                  then
                    (do
                      let w__37 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__37 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (__set_PMSSCR_EL1 (Mk_PMSSCR_EL1_Type w__38)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (__set_PMSSCR_EL1 (Mk_PMSSCR_EL1_Type w__39)))
              else (pure (())))))


end ArmFull.Functions
