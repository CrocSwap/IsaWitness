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
import ArmFull.Fn.M0047
import ArmFull.Fn.M0054
import ArmFull.Fn.M0059
import ArmFull.Fn.M0092
import ArmFull.Fn.M0098
import ArmFull.Fn.M0150
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0184
import ArmFull.Fn.M0185
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
def TLBIMVAHIS_SysRegWrite32_5da1d1a785b555e8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T8 : (BitVec 1) := (_get_HSTR_EL2_Type_T8 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T8 : (BitVec 1) := (_get_HSTR_Type_T8 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__4) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T8 == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T8 == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__11 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
              let w__12 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_TLBI_VA w__11 Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any
                TLBI_AllAttr w__12))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__13 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__14 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (AArch32_TLBI_VA SS_NonSecure Regime_EL2 w__13 Shareability_ISH TLBILevel_Any
                        TLBI_AllAttr w__14)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBIMVAH_SysRegWrite32_4fb355f41064966b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T8 : (BitVec 1) := (_get_HSTR_EL2_Type_T8 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T8 : (BitVec 1) := (_get_HSTR_Type_T8 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__4) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T8 == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T8 == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__11 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
              let w__12 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_TLBI_VA w__11 Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any
                TLBI_AllAttr w__12))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__13 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__14 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (AArch32_TLBI_VA SS_NonSecure Regime_EL2 w__13 Shareability_NSH TLBILevel_Any
                        TLBI_AllAttr w__14)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBIMVAIS_SysRegWrite32_bfc80b2d7757a07f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T8 : (BitVec 1) := (_get_HSTR_EL2_Type_T8 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T8 : (BitVec 1) := (_get_HSTR_Type_T8 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBIS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBIS w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TTLB : (BitVec 1) := (_get_HCR_Type_TTLB w__5)
  let w__6 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  let __HCR2_TTLBIS : (BitVec 1) := (_get_HCR2_Type_TTLBIS w__6)
  let w__7 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FnXS w__7)
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
                                  let w__21 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__21) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TTLBIS == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__23 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__27 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TTLB == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__27 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__31 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCR2_TTLBIS == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__31 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__39 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               if ((← do
                                                    if ((← do
                                                         (IsFeatureImplemented FEAT_XS)) : Bool)
                                                    then
                                                      (do
                                                        let w__33 ← (( do (ELUsingAArch32 EL2) ) :
                                                          SailM Bool )
                                                        (pure (((! w__33) : Bool))))
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
                                  if (w__39 : Bool)
                                  then
                                    (do
                                      let w__40 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                        SecurityState )
                                      let w__41 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                      let w__42 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (AArch32_TLBI_VA w__40 Regime_EL10 w__41 Shareability_ISH
                                        TLBILevel_Any TLBI_ExcludeXS w__42))
                                  else
                                    (do
                                      let w__43 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                        SecurityState )
                                      let w__44 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                      let w__45 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (AArch32_TLBI_VA w__43 Regime_EL10 w__44 Shareability_ISH
                                        TLBILevel_Any TLBI_AllAttr w__45)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__46 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__47 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__48 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_TLBI_VA w__46 Regime_EL10 w__47 Shareability_ISH TLBILevel_Any TLBI_AllAttr
                w__48))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__49 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__50 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_TLBI_VA w__49 Regime_EL30 VMID_NONE Shareability_ISH TLBILevel_Any
                    TLBI_AllAttr w__50))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBIMVALHIS_SysRegWrite32_89a451ea9208e882 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T8 : (BitVec 1) := (_get_HSTR_EL2_Type_T8 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T8 : (BitVec 1) := (_get_HSTR_Type_T8 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__4) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T8 == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T8 == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__11 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
              let w__12 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_TLBI_VA w__11 Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Last
                TLBI_AllAttr w__12))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__13 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__14 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (AArch32_TLBI_VA SS_NonSecure Regime_EL2 w__13 Shareability_ISH TLBILevel_Last
                        TLBI_AllAttr w__14)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBIMVALH_SysRegWrite32_e910bf47238cb4c5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T8 : (BitVec 1) := (_get_HSTR_EL2_Type_T8 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T8 : (BitVec 1) := (_get_HSTR_Type_T8 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__4) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T8 == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T8 == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__11 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
              let w__12 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_TLBI_VA w__11 Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last
                TLBI_AllAttr w__12))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((! (HaveEL EL2)) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__13 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__14 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (AArch32_TLBI_VA SS_NonSecure Regime_EL2 w__13 Shareability_NSH TLBILevel_Last
                        TLBI_AllAttr w__14)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBIMVALIS_SysRegWrite32_ff59541f99afcbcf (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T8 : (BitVec 1) := (_get_HSTR_EL2_Type_T8 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T8 : (BitVec 1) := (_get_HSTR_Type_T8 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBIS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBIS w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TTLB : (BitVec 1) := (_get_HCR_Type_TTLB w__5)
  let w__6 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  let __HCR2_TTLBIS : (BitVec 1) := (_get_HCR2_Type_TTLBIS w__6)
  let w__7 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FnXS w__7)
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
                                  let w__21 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__21) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TTLBIS == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__23 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__27 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TTLB == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__27 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__31 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCR2_TTLBIS == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__31 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__39 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               if ((← do
                                                    if ((← do
                                                         (IsFeatureImplemented FEAT_XS)) : Bool)
                                                    then
                                                      (do
                                                        let w__33 ← (( do (ELUsingAArch32 EL2) ) :
                                                          SailM Bool )
                                                        (pure (((! w__33) : Bool))))
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
                                  if (w__39 : Bool)
                                  then
                                    (do
                                      let w__40 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                        SecurityState )
                                      let w__41 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                      let w__42 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (AArch32_TLBI_VA w__40 Regime_EL10 w__41 Shareability_ISH
                                        TLBILevel_Last TLBI_ExcludeXS w__42))
                                  else
                                    (do
                                      let w__43 ← (( do (SecurityStateAtEL EL1) ) : SailM
                                        SecurityState )
                                      let w__44 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                                      let w__45 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (AArch32_TLBI_VA w__43 Regime_EL10 w__44 Shareability_ISH
                                        TLBILevel_Last TLBI_AllAttr w__45)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__46 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__47 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__48 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_TLBI_VA w__46 Regime_EL10 w__47 Shareability_ISH TLBILevel_Last TLBI_AllAttr
                w__48))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__49 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__50 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_TLBI_VA w__49 Regime_EL30 VMID_NONE Shareability_ISH TLBILevel_Last
                    TLBI_AllAttr w__50))
              else (pure (())))))


end ArmFull.Functions
