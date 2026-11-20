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
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0052
public import ArmFull.Fn.M0072
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0184
public import ArmFull.Fn.M0208
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
              let w__14 ← (( do
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
                                let w__11 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__11) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_TLBIVMALLE1 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_FB == 1#1) : Bool))) ) : SailM Bool )
                  if (w__16 : Bool)
                  then
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
                          (AArch64_TLBI_VMALL w__25 Regime_EL10 w__26 Shareability_ISH TLBI_AllAttr)))
                  else
                    (do
                      let w__32 ← (( do
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
                      if (w__32 : Bool)
                      then
                        (do
                          let w__33 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__34 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__33 Regime_EL10 w__34 Shareability_NSH
                            TLBI_ExcludeXS))
                      else
                        (do
                          let w__35 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__36 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALL w__35 Regime_EL10 w__36 Shareability_NSH TLBI_AllAttr))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__37 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              let w__38 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              if ((((_get_HCR_EL2_Type_E2H w__37) +++ (_get_HCR_EL2_Type_TGE w__38)) == 0b11#2) : Bool)
              then
                (do
                  let w__39 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  (AArch64_TLBI_VMALL w__39 Regime_EL20 VMID_NONE Shareability_NSH TLBI_AllAttr))
              else
                (do
                  let w__40 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__41 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  (AArch64_TLBI_VMALL w__40 Regime_EL10 w__41 Shareability_NSH TLBI_AllAttr)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__42) +++ (_get_HCR_EL2_Type_TGE w__43)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__44 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      (AArch64_TLBI_VMALL w__44 Regime_EL20 VMID_NONE Shareability_NSH TLBI_AllAttr))
                  else
                    (do
                      let w__45 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__46 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALL w__45 Regime_EL10 w__46 Shareability_NSH TLBI_AllAttr)))
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


/-- Type quantifiers: t : Int -/
def TLBI_VMALLS12E1OS_SysOpsWrite_1c9b124b11d1cf42 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              (AArch64_TLBI_VMALLS12 w__4 Regime_EL10 w__5 Shareability_OSH TLBI_AllAttr))
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
                      (AArch64_TLBI_VMALL w__7 Regime_EL10 w__8 Shareability_OSH TLBI_AllAttr))
                  else
                    (do
                      let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALLS12 w__9 Regime_EL10 w__10 Shareability_OSH TLBI_AllAttr)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VMALLS12E1OS_SysOpsWrite_98d1faaee38ba3a7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (AArch64_TLBI_VMALLS12 w__5 Regime_EL10 w__6 Shareability_OSH TLBI_ExcludeXS))
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
                          (AArch64_TLBI_VMALL w__8 Regime_EL10 w__9 Shareability_OSH TLBI_ExcludeXS))
                      else
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__11 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALLS12 w__10 Regime_EL10 w__11 Shareability_OSH
                            TLBI_ExcludeXS)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VMALLS12E1_SysOpsWrite_04d7802e0a5bffbf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              (AArch64_TLBI_VMALLS12 w__4 Regime_EL10 w__5 Shareability_NSH TLBI_AllAttr))
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
                      (AArch64_TLBI_VMALL w__7 Regime_EL10 w__8 Shareability_NSH TLBI_AllAttr))
                  else
                    (do
                      let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      (AArch64_TLBI_VMALLS12 w__9 Regime_EL10 w__10 Shareability_NSH TLBI_AllAttr)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VMALLS12E1_SysOpsWrite_252a42c486a42c51 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (AArch64_TLBI_VMALLS12 w__5 Regime_EL10 w__6 Shareability_NSH TLBI_ExcludeXS))
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
                          (AArch64_TLBI_VMALL w__8 Regime_EL10 w__9 Shareability_NSH TLBI_ExcludeXS))
                      else
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__11 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          (AArch64_TLBI_VMALLS12 w__10 Regime_EL10 w__11 Shareability_NSH
                            TLBI_ExcludeXS)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def PAR_EL1_SysRegRead128_8206ac7c9b0eef57 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_PAR_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_PAR_EL1 w__4)
  let w__5 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_D128En : (BitVec 1) := (_get_HCRX_EL2_Type_D128En w__5)
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
                  else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
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
                      else (pure false)) && ((__HFGRTR_EL2_PAR_EL1 == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__19 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__23 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        (pure ((← do
                              let w__21 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                              (pure (((! w__21) : Bool)))) || ((__HCRX_EL2_D128En == 0#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__25 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
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
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          let w__28 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                          let w__29 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                          let (__tup_0, __tup_1) :=
                            ((Sail.BitVec.extractLsb w__28 127 64), (Sail.BitVec.extractLsb w__29 63
                              0))
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__36 ← (( do
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
                      else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
              if (w__36 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__38 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
                  if (w__38 : Bool)
                  then
                    (do
                      let w__40 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__40 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      let w__41 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                      let w__42 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__41 127 64), (Sail.BitVec.extractLsb w__42 63 0))
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__43 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                  let w__44 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb w__43 127 64), (Sail.BitVec.extractLsb w__44 63 0))
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure (())))))


end ArmFull.Functions
