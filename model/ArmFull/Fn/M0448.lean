module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0062
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0072
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0185
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0244
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
def CPTR_EL2_SysRegWrite_26c85eb30bcb8d19 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TCPAC : (BitVec 1) := (_get_CPTR_EL3_Type_TCPAC w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
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
                      else (pure false)) && ((__CPTR_EL3_TCPAC == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__CPTR_EL3_TCPAC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__16 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__16 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__17 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CPTR_EL2 (Mk_CPTR_EL2_Type w__17))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__18 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CPTR_EL2 (Mk_CPTR_EL2_Type w__18))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CSSELR_EL1_SysRegWrite_cd9c3d82f382498a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID2 : (BitVec 1) := (_get_HCR_EL2_Type_TID2 w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID4 : (BitVec 1) := (_get_HCR_EL2_Type_TID4 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_CSSELR_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_CSSELR_EL1 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID2 == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TID4 == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__15 ← (( do
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
                                    let w__12 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__12) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HFGWTR_EL2_CSSELR_EL1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__15 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__16 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CSSELR_EL1 (Mk_CSSELR_EL1_Type w__16)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__17 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg CSSELR_EL1 (Mk_CSSELR_EL1_Type w__17))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__18 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CSSELR_EL1 (Mk_CSSELR_EL1_Type w__18))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DACR32_EL2_SysRegWrite_94b89018206732e0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (HaveAArch32EL EL1) ) : SailM Bool )
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
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg DACR32_EL2 (Mk_DACR32_EL2_Type w__5))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg DACR32_EL2 (Mk_DACR32_EL2_Type w__6))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DAIF_SysRegWrite_523f21b562245414 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_UMA : (BitVec 1) := (_get_SCTLR_EL1_Type_UMA w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__7 ← (( do
        (pure ((← do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure (((((_get_HCR_EL2_Type_E2H w__4) +++ (_get_HCR_EL2_Type_TGE w__5)) == 0b11#2) : Bool))))
              else (pure false)) || ((__SCTLR_EL1_UMA == 0#1) : Bool))) ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          let w__9 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          let split_vec := (Sail.BitVec.extractLsb w__10 9 6)
          let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__11 with D := (Sail.BitVec.extractLsb split_vec 3 3) }
          let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__12 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
          let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__13 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
          let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__14 with F := (Sail.BitVec.extractLsb split_vec 0 0) }))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          let split_vec := (Sail.BitVec.extractLsb w__15 9 6)
          let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__16 with D := (Sail.BitVec.extractLsb split_vec 3 3) }
          let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__17 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
          let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__18 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
          let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__19 with F := (Sail.BitVec.extractLsb split_vec 0 0) })
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              let split_vec := (Sail.BitVec.extractLsb w__20 9 6)
              let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__21 with D := (Sail.BitVec.extractLsb split_vec 3 3) }
              let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__22 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
              let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__23 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
              let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__24 with F := (Sail.BitVec.extractLsb split_vec 0 0) })
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__25 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let split_vec := (Sail.BitVec.extractLsb w__25 9 6)
                  let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__26 with D := (Sail.BitVec.extractLsb split_vec 3 3) }
                  let w__27 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__27 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
                  let w__28 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__28 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
                  let w__29 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__29 with F := (Sail.BitVec.extractLsb split_vec 0 0) })
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_02aee1e0e30b8f1d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 w__4)
  let w__5 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__5)
  let w__13 ← (( do
    if ((← do
         if ((← do
              let w__6 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
              (pure (((! w__6) : Bool)))) : Bool)
         then
           (do
             let w__7 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
             (pure (((6 ≥b w__7) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
        then
          (do
            let w__10 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2) )
            let w__11 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
            (pure ((((6 +i ((BitVec.toNat w__10) *i 16)) ≥b w__11) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__13 : Bool)
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
              let w__20 ← (( do
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
                          else (pure false)) && ((__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__27 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__31 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__29 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__30 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__29) +++ (_get_MDCR_EL2_Type_TDA
                                    w__30)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__31 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__33 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__33 : Bool)
                          then
                            (do
                              let w__35 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__35 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__39 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__36 ← (( do readReg OSLSR_EL1 ) : SailM
                                             (BitVec 64) )
                                           (pure ((((_get_OSLSR_EL1_Type_OSLK w__36) == 0#1) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaltingAllowed ()))
                                      else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__39 : Bool)
                              then
                                (do
                                  (Halt DebugHalt_SoftwareAccess))
                              else
                                (do
                                  let w__40 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) :
                                    SailM Bool )
                                  if (w__40 : Bool)
                                  then
                                    (do
                                      let w__41 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__42 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                        (BitVec 2) )
                                      let w__43 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg DBGBCR_EL1 (vectorUpdate w__41
                                        (Sail.Int.toNatChecked ((6 +i ((BitVec.toNat w__42) *i 16))))
                                        (Mk_DBGBCR_EL1_Type w__43)))
                                  else
                                    (do
                                      let w__44 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg DBGBCR_EL1 (vectorUpdate w__44 6
                                        (Mk_DBGBCR_EL1_Type w__45)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__52 ← (( do
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
                  if (w__52 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__54 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__54 : Bool)
                      then
                        (do
                          let w__56 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__56 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__60 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__57 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                       (pure ((((_get_OSLSR_EL1_Type_OSLK w__57) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__60 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__61 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM
                                Bool )
                              if (w__61 : Bool)
                              then
                                (do
                                  let w__62 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__63 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                    (BitVec 2) )
                                  let w__64 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg DBGBCR_EL1 (vectorUpdate w__62
                                    (Sail.Int.toNatChecked ((6 +i ((BitVec.toNat w__63) *i 16))))
                                    (Mk_DBGBCR_EL1_Type w__64)))
                              else
                                (do
                                  let w__65 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__66 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg DBGBCR_EL1 (vectorUpdate w__65 6
                                    (Mk_DBGBCR_EL1_Type w__66)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__70 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__67 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                   (pure ((((_get_OSLSR_EL1_Type_OSLK w__67) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__70 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__71 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
                          if (w__71 : Bool)
                          then
                            (do
                              let w__72 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__73 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2)
                                )
                              let w__74 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg DBGBCR_EL1 (vectorUpdate w__72
                                (Sail.Int.toNatChecked ((6 +i ((BitVec.toNat w__73) *i 16))))
                                (Mk_DBGBCR_EL1_Type w__74)))
                          else
                            (do
                              let w__75 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__76 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg DBGBCR_EL1 (vectorUpdate w__75 6 (Mk_DBGBCR_EL1_Type w__76)))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGBCR_EL1_SysRegWrite_061098b9cf5c8fa1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_DBGBCRn_EL1 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_DBGBCRn_EL1 w__4)
  let w__5 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__5)
  let w__13 ← (( do
    if ((← do
         if ((← do
              let w__6 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
              (pure (((! w__6) : Bool)))) : Bool)
         then
           (do
             let w__7 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
             (pure (((5 ≥b w__7) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             (IsFeatureImplemented FEAT_Debugv8p9)) : Bool)
        then
          (do
            let w__10 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2) )
            let w__11 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
            (pure ((((5 +i ((BitVec.toNat w__10) *i 16)) ≥b w__11) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__13 : Bool)
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
              let w__20 ← (( do
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
                          else (pure false)) && ((__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__27 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__31 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__29 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__30 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__29) +++ (_get_MDCR_EL2_Type_TDA
                                    w__30)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__31 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__33 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__33 : Bool)
                          then
                            (do
                              let w__35 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__35 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__39 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__36 ← (( do readReg OSLSR_EL1 ) : SailM
                                             (BitVec 64) )
                                           (pure ((((_get_OSLSR_EL1_Type_OSLK w__36) == 0#1) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaltingAllowed ()))
                                      else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__39 : Bool)
                              then
                                (do
                                  (Halt DebugHalt_SoftwareAccess))
                              else
                                (do
                                  let w__40 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) :
                                    SailM Bool )
                                  if (w__40 : Bool)
                                  then
                                    (do
                                      let w__41 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__42 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                        (BitVec 2) )
                                      let w__43 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg DBGBCR_EL1 (vectorUpdate w__41
                                        (Sail.Int.toNatChecked ((5 +i ((BitVec.toNat w__42) *i 16))))
                                        (Mk_DBGBCR_EL1_Type w__43)))
                                  else
                                    (do
                                      let w__44 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg DBGBCR_EL1 (vectorUpdate w__44 5
                                        (Mk_DBGBCR_EL1_Type w__45)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__52 ← (( do
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
                  if (w__52 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__54 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__54 : Bool)
                      then
                        (do
                          let w__56 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__56 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__60 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__57 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                       (pure ((((_get_OSLSR_EL1_Type_OSLK w__57) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__60 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__61 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM
                                Bool )
                              if (w__61 : Bool)
                              then
                                (do
                                  let w__62 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__63 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                    (BitVec 2) )
                                  let w__64 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg DBGBCR_EL1 (vectorUpdate w__62
                                    (Sail.Int.toNatChecked ((5 +i ((BitVec.toNat w__63) *i 16))))
                                    (Mk_DBGBCR_EL1_Type w__64)))
                              else
                                (do
                                  let w__65 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__66 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg DBGBCR_EL1 (vectorUpdate w__65 5
                                    (Mk_DBGBCR_EL1_Type w__66)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__70 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__67 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                   (pure ((((_get_OSLSR_EL1_Type_OSLK w__67) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__70 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__71 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
                          if (w__71 : Bool)
                          then
                            (do
                              let w__72 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__73 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2)
                                )
                              let w__74 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg DBGBCR_EL1 (vectorUpdate w__72
                                (Sail.Int.toNatChecked ((5 +i ((BitVec.toNat w__73) *i 16))))
                                (Mk_DBGBCR_EL1_Type w__74)))
                          else
                            (do
                              let w__75 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__76 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg DBGBCR_EL1 (vectorUpdate w__75 5 (Mk_DBGBCR_EL1_Type w__76)))))
                  else (pure (()))))))


end ArmFull.Functions
