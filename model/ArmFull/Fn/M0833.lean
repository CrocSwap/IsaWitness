import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0042
import ArmFull.Fn.M0044
import ArmFull.Fn.M0054
import ArmFull.Fn.M0059
import ArmFull.Fn.M0081
import ArmFull.Fn.M0082
import ArmFull.Fn.M0092
import ArmFull.Fn.M0098
import ArmFull.Fn.M0150
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0184
import ArmFull.Fn.M0185
import ArmFull.Fn.M0201
import ArmFull.Fn.M0202
import ArmFull.Fn.M0254
import ArmFull.Fn.M0260

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
def TLBIMVAL_SysRegWrite32_db84fa64000a2011 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FB : (BitVec 1) := (_get_HCR_EL2_Type_FB w__5)
  let w__6 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FnXS w__6)
  let w__7 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_FB : (BitVec 1) := (_get_HCR_Type_FB w__7)
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
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__9 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__9) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T8 == 1#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__15 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T8 == 1#1) : Bool))) ) : SailM Bool )
              if (w__15 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__17 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__17) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__23 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TTLB == 1#1) : Bool))) ) : SailM Bool )
                      if (w__23 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__27 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__25 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__25) : Bool))))
                                  else (pure false)) && ((__HCR_EL2_FB == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__27 : Bool)
                          then
                            (do
                              let w__33 ← (( do
                                (pure ((← do
                                      if ((← do
                                           if ((← do
                                                (IsFeatureImplemented FEAT_XS)) : Bool)
                                           then
                                             (do
                                               (IsFeatureImplemented FEAT_HCX))
                                           else (pure false)) : Bool)
                                      then
                                        (do
                                          (IsHCRXEL2Enabled ()))
                                      else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__33 : Bool)
                              then
                                (do
                                  let w__34 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                    SecurityState )
                                  let w__35 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                  let w__36 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (AArch32_TLBI_VA w__34 Regime_EL10 w__35 Shareability_ISH
                                    TLBILevel_Last TLBI_ExcludeXS w__36))
                              else
                                (do
                                  let w__37 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                    SecurityState )
                                  let w__38 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                  let w__39 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (AArch32_TLBI_VA w__37 Regime_EL10 w__38 Shareability_ISH
                                    TLBILevel_Last TLBI_AllAttr w__39)))
                          else
                            (do
                              let w__43 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCR_FB == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__43 : Bool)
                              then
                                (do
                                  let w__44 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                    SecurityState )
                                  let w__45 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                  let w__46 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (AArch32_TLBI_VA w__44 Regime_EL10 w__45 Shareability_ISH
                                    TLBILevel_Last TLBI_AllAttr w__46))
                              else
                                (do
                                  let w__54 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               if ((← do
                                                    if ((← do
                                                         (IsFeatureImplemented FEAT_XS)) : Bool)
                                                    then
                                                      (do
                                                        let w__48 ← (( do (ELUsingAArch32 EL2) ) :
                                                          SailM Bool )
                                                        (pure (((! w__48) : Bool))))
                                                    else (pure false)) : Bool)
                                               then
                                                 (do
                                                   (IsFeatureImplemented FEAT_HCX))
                                               else (pure false)) : Bool)
                                          then
                                            (do
                                              (IsHCRXEL2Enabled ()))
                                          else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__54 : Bool)
                                  then
                                    (do
                                      let w__55 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                        SecurityState )
                                      let w__56 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                      let w__57 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (AArch32_TLBI_VA w__55 Regime_EL10 w__56 Shareability_NSH
                                        TLBILevel_Last TLBI_ExcludeXS w__57))
                                  else
                                    (do
                                      let w__58 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                        SecurityState )
                                      let w__59 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                      let w__60 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (AArch32_TLBI_VA w__58 Regime_EL10 w__59 Shareability_NSH
                                        TLBILevel_Last TLBI_AllAttr w__60)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__61 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__62 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__63 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_TLBI_VA w__61 Regime_EL10 w__62 Shareability_NSH TLBILevel_Last TLBI_AllAttr
                w__63))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__64 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__65 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_TLBI_VA w__64 Regime_EL30 VMID_NONE Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr w__65))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBIMVA_SysRegWrite32_f66a0ca0f4cc9ff0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FB : (BitVec 1) := (_get_HCR_EL2_Type_FB w__5)
  let w__6 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FnXS w__6)
  let w__7 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_FB : (BitVec 1) := (_get_HCR_Type_FB w__7)
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
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__9 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__9) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T8 == 1#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__15 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T8 == 1#1) : Bool))) ) : SailM Bool )
              if (w__15 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__17 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__17) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__23 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TTLB == 1#1) : Bool))) ) : SailM Bool )
                      if (w__23 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__27 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__25 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__25) : Bool))))
                                  else (pure false)) && ((__HCR_EL2_FB == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__27 : Bool)
                          then
                            (do
                              let w__33 ← (( do
                                (pure ((← do
                                      if ((← do
                                           if ((← do
                                                (IsFeatureImplemented FEAT_XS)) : Bool)
                                           then
                                             (do
                                               (IsFeatureImplemented FEAT_HCX))
                                           else (pure false)) : Bool)
                                      then
                                        (do
                                          (IsHCRXEL2Enabled ()))
                                      else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__33 : Bool)
                              then
                                (do
                                  let w__34 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                    SecurityState )
                                  let w__35 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                  let w__36 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (AArch32_TLBI_VA w__34 Regime_EL10 w__35 Shareability_ISH
                                    TLBILevel_Any TLBI_ExcludeXS w__36))
                              else
                                (do
                                  let w__37 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                    SecurityState )
                                  let w__38 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                  let w__39 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (AArch32_TLBI_VA w__37 Regime_EL10 w__38 Shareability_ISH
                                    TLBILevel_Any TLBI_AllAttr w__39)))
                          else
                            (do
                              let w__43 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCR_FB == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__43 : Bool)
                              then
                                (do
                                  let w__44 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                    SecurityState )
                                  let w__45 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                  let w__46 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (AArch32_TLBI_VA w__44 Regime_EL10 w__45 Shareability_ISH
                                    TLBILevel_Any TLBI_AllAttr w__46))
                              else
                                (do
                                  let w__54 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               if ((← do
                                                    if ((← do
                                                         (IsFeatureImplemented FEAT_XS)) : Bool)
                                                    then
                                                      (do
                                                        let w__48 ← (( do (ELUsingAArch32 EL2) ) :
                                                          SailM Bool )
                                                        (pure (((! w__48) : Bool))))
                                                    else (pure false)) : Bool)
                                               then
                                                 (do
                                                   (IsFeatureImplemented FEAT_HCX))
                                               else (pure false)) : Bool)
                                          then
                                            (do
                                              (IsHCRXEL2Enabled ()))
                                          else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__54 : Bool)
                                  then
                                    (do
                                      let w__55 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                        SecurityState )
                                      let w__56 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                      let w__57 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (AArch32_TLBI_VA w__55 Regime_EL10 w__56 Shareability_NSH
                                        TLBILevel_Any TLBI_ExcludeXS w__57))
                                  else
                                    (do
                                      let w__58 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                        SecurityState )
                                      let w__59 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                      let w__60 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (AArch32_TLBI_VA w__58 Regime_EL10 w__59 Shareability_NSH
                                        TLBILevel_Any TLBI_AllAttr w__60)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__61 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__62 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__63 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_TLBI_VA w__61 Regime_EL10 w__62 Shareability_NSH TLBILevel_Any TLBI_AllAttr
                w__63))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__64 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__65 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_TLBI_VA w__64 Regime_EL30 VMID_NONE Shareability_NSH TLBILevel_Any
                    TLBI_AllAttr w__65))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TPIDRPRW_SysRegWrite32_5caaac18c68f924b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__2)
  let w__3 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__5) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__13 ← (( do
                    if (((HaveEL EL3) : Bool) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL3))
                    else (pure false) ) : SailM Bool )
                  if (w__13 : Bool)
                  then
                    (do
                      let w__14 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TPIDRPRW_NS_write w__14))
                  else
                    (do
                      let w__15 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TPIDRPRW_write w__15)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__17 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TPIDRPRW_NS_write w__18))
              else
                (do
                  let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TPIDRPRW_write w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__20 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg TPIDRPRW_S w__20)
                  else
                    (do
                      let w__21 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TPIDRPRW_NS_write w__21)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TPIDRURO_SysRegWrite32_2b144f3027758b96 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__2)
  let w__3 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__5) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__13 ← (( do
                    if (((HaveEL EL3) : Bool) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL3))
                    else (pure false) ) : SailM Bool )
                  if (w__13 : Bool)
                  then
                    (do
                      let w__14 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TPIDRURO_NS_write w__14))
                  else
                    (do
                      let w__15 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TPIDRURO_write w__15)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__17 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TPIDRURO_NS_write w__18))
              else
                (do
                  let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TPIDRURO_write w__19)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__20 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg TPIDRURO_S w__20)
                  else
                    (do
                      let w__21 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TPIDRURO_NS_write w__21)))
              else (pure (())))))


end ArmFull.Functions
