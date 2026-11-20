module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0052
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0148
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0184
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
def TLBI_VALE2_SysOpsWrite_2fb1c62ae3ec4f94 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
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
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VA w__5 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr w__6))
              else
                (do
                  let w__7 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VA w__7 Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr w__8)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__9 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__9) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__10 Regime_EL20 VMID_NONE Shareability_NSH
                            TLBILevel_Last TLBI_AllAttr w__11))
                      else
                        (do
                          let w__12 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__12 Regime_EL2 VMID_NONE Shareability_NSH
                            TLBILevel_Last TLBI_AllAttr w__13))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VMALLE1IS_SysOpsWrite_8653d883f8306258 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBIS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBIS w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVMALLE1IS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVMALLE1IS w__4)
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
                      (EL2Enabled ())) && ((__HCR_EL2_TTLBIS == 1#1) : Bool))) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
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
                          else (pure false)) && ((__HFGITR_EL2_TLBIVMALLE1IS == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__22 ← (( do
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
                      if (w__22 : Bool)
                      then
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__23 Regime_EL10 w__24 Shareability_ISH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__25 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__26 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__25 Regime_EL10 w__26 Shareability_ISH TLBI_AllAttr))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              if ((((_get_HCR_EL2_Type_E2H w__27) +++ (_get_HCR_EL2_Type_TGE w__28)) == 0b11#2) : Bool)
              then
                (do
                  let w__29 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  (AArch64_TLBI_VMALL w__29 Regime_EL20 VMID_NONE Shareability_ISH TLBI_AllAttr))
              else
                (do
                  let w__30 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__31 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  (AArch64_TLBI_VMALL w__30 Regime_EL10 w__31 Shareability_ISH TLBI_AllAttr)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__32) +++ (_get_HCR_EL2_Type_TGE w__33)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__34 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      (AArch64_TLBI_VMALL w__34 Regime_EL20 VMID_NONE Shareability_ISH TLBI_AllAttr))
                  else
                    (do
                      let w__35 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__36 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALL w__35 Regime_EL10 w__36 Shareability_ISH TLBI_AllAttr)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VMALLE1IS_SysOpsWrite_b92e6f7b045bcd26 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBIS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBIS w__2)
  let w__3 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FGTnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FGTnXS w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVMALLE1IS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVMALLE1IS w__4)
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
                          (EL2Enabled ())) && ((__HCR_EL2_TTLBIS == 1#1) : Bool))) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__22 ← (( do
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
                                            if ((← do
                                                 let w__13 ← (( do (HaveEL EL3) ) : SailM Bool )
                                                 (pure (((! w__13) : Bool)))) : Bool)
                                            then (pure true)
                                            else
                                              (do
                                                let w__14 ← (( do readReg SCR_EL3 ) : SailM
                                                  (BitVec 64) )
                                                (pure ((((_get_SCR_EL3_Type_FGTEn w__14) == 1#1) : Bool)))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_HCX))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__19 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                        (pure (((! w__19) : Bool)))) || ((__HCRX_EL2_FGTnXS == 0#1) : Bool))))
                              else (pure false)) && ((__HFGITR_EL2_TLBIVMALLE1IS == 1#1) : Bool))) )
                        : SailM Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__23 Regime_EL10 w__24 Shareability_ISH
                            TLBI_ExcludeXS)))))
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
                      (AArch64_TLBI_VMALL w__27 Regime_EL20 VMID_NONE Shareability_ISH
                        TLBI_ExcludeXS))
                  else
                    (do
                      let w__28 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__29 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALL w__28 Regime_EL10 w__29 Shareability_ISH TLBI_ExcludeXS)))
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
                          (AArch64_TLBI_VMALL w__32 Regime_EL20 VMID_NONE Shareability_ISH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__33 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__34 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__33 Regime_EL10 w__34 Shareability_ISH
                            TLBI_ExcludeXS)))
                  else (pure (()))))))


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
                          else (pure false)) && ((__HFGITR_EL2_TLBIVMALLE1OS == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__22 ← (( do
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
                      if (w__22 : Bool)
                      then
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__23 Regime_EL10 w__24 Shareability_OSH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__25 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__26 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__25 Regime_EL10 w__26 Shareability_OSH TLBI_AllAttr))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              if ((((_get_HCR_EL2_Type_E2H w__27) +++ (_get_HCR_EL2_Type_TGE w__28)) == 0b11#2) : Bool)
              then
                (do
                  let w__29 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  (AArch64_TLBI_VMALL w__29 Regime_EL20 VMID_NONE Shareability_OSH TLBI_AllAttr))
              else
                (do
                  let w__30 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__31 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  (AArch64_TLBI_VMALL w__30 Regime_EL10 w__31 Shareability_OSH TLBI_AllAttr)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__32) +++ (_get_HCR_EL2_Type_TGE w__33)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__34 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      (AArch64_TLBI_VMALL w__34 Regime_EL20 VMID_NONE Shareability_OSH TLBI_AllAttr))
                  else
                    (do
                      let w__35 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__36 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALL w__35 Regime_EL10 w__36 Shareability_OSH TLBI_AllAttr)))
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
                      let w__22 ← (( do
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
                                            if ((← do
                                                 let w__13 ← (( do (HaveEL EL3) ) : SailM Bool )
                                                 (pure (((! w__13) : Bool)))) : Bool)
                                            then (pure true)
                                            else
                                              (do
                                                let w__14 ← (( do readReg SCR_EL3 ) : SailM
                                                  (BitVec 64) )
                                                (pure ((((_get_SCR_EL3_Type_FGTEn w__14) == 1#1) : Bool)))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_HCX))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__19 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                        (pure (((! w__19) : Bool)))) || ((__HCRX_EL2_FGTnXS == 0#1) : Bool))))
                              else (pure false)) && ((__HFGITR_EL2_TLBIVMALLE1OS == 1#1) : Bool))) )
                        : SailM Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__23 Regime_EL10 w__24 Shareability_OSH
                            TLBI_ExcludeXS)))))
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
                      (AArch64_TLBI_VMALL w__27 Regime_EL20 VMID_NONE Shareability_OSH
                        TLBI_ExcludeXS))
                  else
                    (do
                      let w__28 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__29 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALL w__28 Regime_EL10 w__29 Shareability_OSH TLBI_ExcludeXS)))
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
                          (AArch64_TLBI_VMALL w__32 Regime_EL20 VMID_NONE Shareability_OSH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__33 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__34 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__33 Regime_EL10 w__34 Shareability_OSH
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
                  let w__20 ← (( do
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
                                        if ((← do
                                             let w__11 ← (( do (HaveEL EL3) ) : SailM Bool )
                                             (pure (((! w__11) : Bool)))) : Bool)
                                        then (pure true)
                                        else
                                          (do
                                            let w__12 ← (( do readReg SCR_EL3 ) : SailM
                                              (BitVec 64) )
                                            (pure ((((_get_SCR_EL3_Type_FGTEn w__12) == 1#1) : Bool)))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_HCX))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__17 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                    (pure (((! w__17) : Bool)))) || ((__HCRX_EL2_FGTnXS == 0#1) : Bool))))
                          else (pure false)) && ((__HFGITR_EL2_TLBIVMALLE1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__20 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__22 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_FB == 1#1) : Bool))) ) : SailM Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__23 Regime_EL10 w__24 Shareability_ISH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__25 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__26 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__25 Regime_EL10 w__26 Shareability_NSH
                            TLBI_ExcludeXS)))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__27) +++ (_get_HCR_EL2_Type_TGE w__28)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__29 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      (AArch64_TLBI_VMALL w__29 Regime_EL20 VMID_NONE Shareability_NSH
                        TLBI_ExcludeXS))
                  else
                    (do
                      let w__30 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__31 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALL w__30 Regime_EL10 w__31 Shareability_NSH TLBI_ExcludeXS)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      if ((((_get_HCR_EL2_Type_E2H w__32) +++ (_get_HCR_EL2_Type_TGE w__33)) == 0b11#2) : Bool)
                      then
                        (do
                          let w__34 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          (AArch64_TLBI_VMALL w__34 Regime_EL20 VMID_NONE Shareability_NSH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__35 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__36 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__35 Regime_EL10 w__36 Shareability_NSH
                            TLBI_ExcludeXS)))
                  else (pure (()))))))


end ArmFull.Functions
