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
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0148
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0184
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0227
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0253
public import ArmFull.Fn.M0258 set_option backward.proofsInPublic true @[expose] public section

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
def DTLBIMVA_SysRegWrite32_4d3bdab2ea1d893d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T8 : (BitVec 1) := (_get_HSTR_EL2_Type_T8 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T8 : (BitVec 1) := (_get_HSTR_Type_T8 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TTLB : (BitVec 1) := (_get_HCR_Type_TTLB w__4)
  let w__5 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FnXS w__5)
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
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__7 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__7) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T8 == 1#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T8 == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__17 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__15) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TTLB == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__29 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            if ((← do
                                                 (IsFeatureImplemented FEAT_XS)) : Bool)
                                            then
                                              (do
                                                let w__23 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                  Bool )
                                                (pure (((! w__23) : Bool))))
                                            else (pure false)) : Bool)
                                       then
                                         (do
                                           (IsFeatureImplemented FEAT_HCX))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      (IsHCRXEL2Enabled ()))
                                  else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__29 : Bool)
                          then
                            (do
                              let w__30 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                              let w__31 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                              let w__32 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (AArch32_DTLBI_VA w__30 Regime_EL10 w__31 Shareability_NSH
                                TLBILevel_Any TLBI_ExcludeXS w__32))
                          else
                            (do
                              let w__33 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                              let w__34 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                              let w__35 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (AArch32_DTLBI_VA w__33 Regime_EL10 w__34 Shareability_NSH
                                TLBILevel_Any TLBI_AllAttr w__35)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__36 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__37 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__38 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_DTLBI_VA w__36 Regime_EL10 w__37 Shareability_NSH TLBILevel_Any TLBI_AllAttr
                w__38))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__39 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__40 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_DTLBI_VA w__39 Regime_EL30 VMID_NONE Shareability_NSH TLBILevel_Any
                    TLBI_AllAttr w__40))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DVPRCTX_SysRegWrite32_60021502cabbda39 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_EnRCTX : (BitVec 1) := (_get_SCTLR_EL1_Type_EnRCTX w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  let __SCTLR_EnRCTX : (BitVec 1) := (_get_SCTLR_Type_EnRCTX w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  let w__5 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__5)
  let w__6 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__6)
  let w__7 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__7)
  let w__8 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DVPRCTX : (BitVec 1) := (_get_HFGITR_EL2_Type_DVPRCTX w__8)
  let w__9 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_EnRCTX : (BitVec 1) := (_get_SCTLR_EL2_Type_EnRCTX w__9)
  let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__10)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__17 ← (( do
        (pure ((← do
              if ((← do
                   let w__11 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__11) : Bool)))) : Bool)
              then
                (do
                  let w__15 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__13) +++ (_get_HCR_EL2_Type_TGE w__14)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__15) : Bool))))
              else (pure false)) && ((__SCTLR_EL1_EnRCTX == 0#1) : Bool))) ) : SailM Bool )
      if (w__17 : Bool)
      then
        (do
          let w__21 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__19 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__19) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__21 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
      else
        (do
          let w__23 ← (( do
            (pure ((← do
                  (ELUsingAArch32 EL1)) && ((__SCTLR_EnRCTX == 0#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
          then
            (do
              let w__27 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__25 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__25) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__27 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              let w__38 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               let w__33 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                               (pure (((! w__33) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__35 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__35) +++ (_get_HCR_EL2_Type_TGE w__36)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__38 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__42 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__42 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__54 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             if ((← do
                                                  (EL2Enabled ())) : Bool)
                                             then
                                               (do
                                                 let w__44 ← (( do (ELUsingAArch32 EL1) ) : SailM
                                                   Bool )
                                                 (pure (((! w__44) : Bool))))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            let w__46 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            let w__47 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            (pure (((((_get_HCR_EL2_Type_E2H w__46) +++ (_get_HCR_EL2_Type_TGE
                                                    w__47)) != 0b11#2) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_FGT))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__51 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__51) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HFGITR_EL2_DVPRCTX == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__54 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__61 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            (EL2Enabled ())) : Bool)
                                       then
                                         (do
                                           let w__56 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                           (pure (((! w__56) : Bool))))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__58 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      let w__59 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      (pure (((((_get_HCR_EL2_Type_E2H w__58) +++ (_get_HCR_EL2_Type_TGE
                                              w__59)) == 0b11#2) : Bool))))
                                  else (pure false)) && ((__SCTLR_EL2_EnRCTX == 0#1) : Bool))) ) :
                            SailM Bool )
                          if (w__61 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__62 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (AArch32_RestrictPrediction w__62 RestrictType_DataValue))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__66 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__64 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__64) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__66 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__70 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__70 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__74 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__72 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__72) : Bool))))
                          else (pure false)) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
                  if (w__74 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__75 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (AArch32_RestrictPrediction w__75 RestrictType_DataValue)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__76 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_RestrictPrediction w__76 RestrictType_DataValue))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__77 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_RestrictPrediction w__77 RestrictType_DataValue))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ERRSELR_SysRegWrite32_e1b5ff755f2cd46d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TERR : (BitVec 1) := (_get_SCR_EL3_Type_TERR w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TWERR : (BitVec 1) := (_get_SCR_EL3_Type_TWERR w__2)
  let w__3 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_TERR : (BitVec 1) := (_get_SCR_Type_TERR w__3)
  let w__4 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__4)
  let w__5 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TERR : (BitVec 1) := (_get_HCR_EL2_Type_TERR w__6)
  let w__7 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  let __HCR2_TERR : (BitVec 1) := (_get_HCR2_Type_TERR w__7)
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__8.M
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__18 ← (( do
            (pure ((← do
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
                                let w__12 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__12) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__16 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__16) : Bool))))
                  else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__28 ← (( do
                (pure ((← do
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
                                    let w__22 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__22) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__26 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__26) : Bool))))
                      else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__38 ← (( do
                    (pure ((← do
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
                                        let w__32 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__32) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SCR_TERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__38 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__42 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__40 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__40) : Bool))))
                              else (pure false)) && ((__HSTR_EL2_T5 == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__42 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__46 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HSTR_T5 == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__46 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__50 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__48 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__48) : Bool))))
                                      else (pure false)) && ((__HCR_EL2_TERR == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__50 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__54 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__HCR2_TERR == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__54 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__58 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__56 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__56) : Bool))))
                                              else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__58 : Bool)
                                      then
                                        (do
                                          let w__61 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__60 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__60) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__61 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x03#8))))
                                      else
                                        (do
                                          let w__65 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (HaveEL EL3)) : Bool)
                                                  then
                                                    (do
                                                      let w__63 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__63) : Bool))))
                                                  else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__65 : Bool)
                                          then
                                            (do
                                              let w__68 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__67 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__67) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__68 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_AArch32SystemAccessTrap EL3
                                                    (BitVec.toNat 0x03#8))))
                                          else
                                            (do
                                              let w__73 ← (( do
                                                (pure ((← do
                                                      (pure ((← do
                                                            if ((← do
                                                                 (HaveEL EL3)) : Bool)
                                                            then
                                                              (do
                                                                (ELUsingAArch32 EL3))
                                                            else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) && ((__SCR_TERR == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__73 : Bool)
                                              then
                                                (do
                                                  let w__76 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__75 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__75) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__76 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch32_TakeMonitorTrapException ())))
                                              else
                                                (do
                                                  let w__77 ← (( do (R_read t) ) : SailM
                                                    (BitVec 32) )
                                                  (ERRSELR_write (Mk_ERRSELR_Type w__77)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__87 ← (( do
                (pure ((← do
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
                                    let w__81 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__81) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__85 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__85) : Bool))))
                      else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__87 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__97 ← (( do
                    (pure ((← do
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
                                        let w__91 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__91) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__95 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__95) : Bool))))
                          else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__97 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__107 ← (( do
                        (pure ((← do
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
                                            let w__101 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__101) == 1#1) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL3))
                              else (pure false)) && ((__SCR_TERR == 1#1) : Bool))) ) : SailM Bool )
                      if (w__107 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__111 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__109 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__109) : Bool))))
                                  else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__111 : Bool)
                          then
                            (do
                              let w__114 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__113 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__113) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__114 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__118 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__116 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__116) : Bool))))
                                      else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__118 : Bool)
                              then
                                (do
                                  let w__121 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__120 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__120) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__121 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  let w__125 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL3))
                                          else (pure false)) && ((__SCR_TERR == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__125 : Bool)
                                  then
                                    (do
                                      let w__128 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__127 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__127) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__128 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch32_TakeMonitorTrapException ())))
                                  else
                                    (do
                                      let w__129 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (ERRSELR_write (Mk_ERRSELR_Type w__129)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then
                    (do
                      (AArch32_TakeMonitorTrapException ()))
                  else
                    (do
                      let w__130 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (ERRSELR_write (Mk_ERRSELR_Type w__130))))
              else (pure (())))))


end ArmFull.Functions
