import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0044
import ArmFull.Fn.M0052
import ArmFull.Fn.M0092
import ArmFull.Fn.M0098
import ArmFull.Fn.M0149
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0184
import ArmFull.Fn.M0185
import ArmFull.Fn.M0254

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
def TLBI_VMALLE1OS_SysOpsWrite_71ae489ebaf642d0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBOS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBOS w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVMALLE1OS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVMALLE1OS w__4)
  let w__5 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FnXS w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__9 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TTLBOS == 1#1) : Bool))) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_TLBIVMALLE1OS == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__20 ← (( do
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
                              else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          let w__21 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__22 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__21 Regime_EL10 w__22 Shareability_OSH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__23 Regime_EL10 w__24 Shareability_OSH TLBI_AllAttr))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              if ((((_get_HCR_EL2_Type_E2H w__25) +++ (_get_HCR_EL2_Type_TGE w__26)) == 0b11#2) : Bool)
              then
                (do
                  let w__27 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  (AArch64_TLBI_VMALL w__27 Regime_EL20 VMID_NONE Shareability_OSH TLBI_AllAttr))
              else
                (do
                  let w__28 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__29 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  (AArch64_TLBI_VMALL w__28 Regime_EL10 w__29 Shareability_OSH TLBI_AllAttr)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__30) +++ (_get_HCR_EL2_Type_TGE w__31)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__32 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      (AArch64_TLBI_VMALL w__32 Regime_EL20 VMID_NONE Shareability_OSH TLBI_AllAttr))
                  else
                    (do
                      let w__33 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__34 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALL w__33 Regime_EL10 w__34 Shareability_OSH TLBI_AllAttr)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VMALLE1OS_SysOpsWrite_9b7b764d81828e24 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBOS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBOS w__2)
  let w__3 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FGTnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FGTnXS w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVMALLE1OS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVMALLE1OS w__4)
  let w__5 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__7 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__9 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TTLBOS == 1#1) : Bool))) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             if ((← do
                                                  (EL2Enabled ())) : Bool)
                                             then
                                               (do
                                                 (IsFeatureImplemented FEAT_FGT))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            if (((! (HaveEL EL3)) : Bool) : Bool)
                                            then (pure true)
                                            else
                                              (do
                                                let w__13 ← (( do readReg SCR_EL3 ) : SailM
                                                  (BitVec 64) )
                                                (pure ((((_get_SCR_EL3_Type_FGTEn w__13) == 1#1) : Bool)))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_HCX))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__18 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                        (pure (((! w__18) : Bool)))) || ((__HCRX_EL2_FGTnXS == 0#1) : Bool))))
                              else (pure false)) && ((__HFGITR_EL2_TLBIVMALLE1OS == 1#1) : Bool))) )
                        : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__22 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__23 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__22 Regime_EL10 w__23 Shareability_OSH
                            TLBI_ExcludeXS)))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__24) +++ (_get_HCR_EL2_Type_TGE w__25)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__26 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      (AArch64_TLBI_VMALL w__26 Regime_EL20 VMID_NONE Shareability_OSH
                        TLBI_ExcludeXS))
                  else
                    (do
                      let w__27 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__28 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALL w__27 Regime_EL10 w__28 Shareability_OSH TLBI_ExcludeXS)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      if ((((_get_HCR_EL2_Type_E2H w__29) +++ (_get_HCR_EL2_Type_TGE w__30)) == 0b11#2) : Bool)
                      then
                        (do
                          let w__31 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          (AArch64_TLBI_VMALL w__31 Regime_EL20 VMID_NONE Shareability_OSH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__32 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__33 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__32 Regime_EL10 w__33 Shareability_OSH
                            TLBI_ExcludeXS)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VMALLE1_SysOpsWrite_bcd60b78fb7e2b4a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FGTnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FGTnXS w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVMALLE1 : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVMALLE1 w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FB : (BitVec 1) := (_get_HCR_EL2_Type_FB w__4)
  let w__5 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__7 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             (IsFeatureImplemented FEAT_FGT))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        if (((! (HaveEL EL3)) : Bool) : Bool)
                                        then (pure true)
                                        else
                                          (do
                                            let w__11 ← (( do readReg SCR_EL3 ) : SailM
                                              (BitVec 64) )
                                            (pure ((((_get_SCR_EL3_Type_FGTEn w__11) == 1#1) : Bool)))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_HCX))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__16 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                    (pure (((! w__16) : Bool)))) || ((__HCRX_EL2_FGTnXS == 0#1) : Bool))))
                          else (pure false)) && ((__HFGITR_EL2_TLBIVMALLE1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_FB == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          let w__22 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__23 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__22 Regime_EL10 w__23 Shareability_ISH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__24 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__25 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__24 Regime_EL10 w__25 Shareability_NSH
                            TLBI_ExcludeXS)))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__26) +++ (_get_HCR_EL2_Type_TGE w__27)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__28 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      (AArch64_TLBI_VMALL w__28 Regime_EL20 VMID_NONE Shareability_NSH
                        TLBI_ExcludeXS))
                  else
                    (do
                      let w__29 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__30 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALL w__29 Regime_EL10 w__30 Shareability_NSH TLBI_ExcludeXS)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      if ((((_get_HCR_EL2_Type_E2H w__31) +++ (_get_HCR_EL2_Type_TGE w__32)) == 0b11#2) : Bool)
                      then
                        (do
                          let w__33 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          (AArch64_TLBI_VMALL w__33 Regime_EL20 VMID_NONE Shareability_NSH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__34 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__35 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__34 Regime_EL10 w__35 Shareability_NSH
                            TLBI_ExcludeXS)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VMALLE1_SysOpsWrite_d94c690b16646ffd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVMALLE1 : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVMALLE1 w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FB : (BitVec 1) := (_get_HCR_EL2_Type_FB w__4)
  let w__5 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FnXS w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_TLBIVMALLE1 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_FB == 1#1) : Bool))) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__20 ← (( do
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
                              else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          let w__21 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__22 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__21 Regime_EL10 w__22 Shareability_ISH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__23 Regime_EL10 w__24 Shareability_ISH TLBI_AllAttr)))
                  else
                    (do
                      let w__30 ← (( do
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
                              else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__30 : Bool)
                      then
                        (do
                          let w__31 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__32 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__31 Regime_EL10 w__32 Shareability_NSH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__33 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__34 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__33 Regime_EL10 w__34 Shareability_NSH TLBI_AllAttr))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__35 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              if ((((_get_HCR_EL2_Type_E2H w__35) +++ (_get_HCR_EL2_Type_TGE w__36)) == 0b11#2) : Bool)
              then
                (do
                  let w__37 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  (AArch64_TLBI_VMALL w__37 Regime_EL20 VMID_NONE Shareability_NSH TLBI_AllAttr))
              else
                (do
                  let w__38 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__39 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  (AArch64_TLBI_VMALL w__38 Regime_EL10 w__39 Shareability_NSH TLBI_AllAttr)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__40) +++ (_get_HCR_EL2_Type_TGE w__41)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__42 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      (AArch64_TLBI_VMALL w__42 Regime_EL20 VMID_NONE Shareability_NSH TLBI_AllAttr))
                  else
                    (do
                      let w__43 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__44 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALL w__43 Regime_EL10 w__44 Shareability_NSH TLBI_AllAttr)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VMALLS12E1IS_SysOpsWrite_3dfe7b46e2ce9676 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              (AArch64_TLBI_VMALLS12 w__4 Regime_EL10 w__5 Shareability_ISH TLBI_AllAttr))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__6 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__6) : Bool)
                  then
                    (do
                      let w__7 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__8 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALL w__7 Regime_EL10 w__8 Shareability_ISH TLBI_AllAttr))
                  else
                    (do
                      let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALLS12 w__9 Regime_EL10 w__10 Shareability_ISH TLBI_AllAttr)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VMALLS12E1IS_SysOpsWrite_94de5730f49bdd76 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__4 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__4 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  (AArch64_TLBI_VMALLS12 w__5 Regime_EL10 w__6 Shareability_ISH TLBI_ExcludeXS))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__7 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__7) : Bool)
                      then
                        (do
                          let w__8 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__8 Regime_EL10 w__9 Shareability_ISH TLBI_ExcludeXS))
                      else
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__11 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALLS12 w__10 Regime_EL10 w__11 Shareability_ISH
                            TLBI_ExcludeXS)))
                  else (pure (()))))))


end ArmFull.Functions
