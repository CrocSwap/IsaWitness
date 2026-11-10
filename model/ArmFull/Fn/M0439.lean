import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0048
import ArmFull.Fn.M0050
import ArmFull.Fn.M0062
import ArmFull.Fn.M0064
import ArmFull.Fn.M0072
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0146
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0185
import ArmFull.Fn.M0196
import ArmFull.Fn.M0246
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
def CNTV_TVAL_EL0_SysRegWrite_1d3b2670e7bc3a02 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let w__6 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  let w__7 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                  writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type
                    ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                          (Sail.BitVec.extractLsb w__5 31 0) 64)) + w__6)) - w__7)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
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
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__11 : Bool)
                  then
                    (do
                      let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      let w__13 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__14 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                      writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type
                        ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                              (Sail.BitVec.extractLsb w__12 31 0) 64)) + w__13)) - w__14)))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CONTEXTIDR_EL2_SysRegWrite_8c6e5eeae39e62ee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg CONTEXTIDR_EL2 (Mk_CONTEXTIDR_EL2_Type w__4))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CONTEXTIDR_EL2 (Mk_CONTEXTIDR_EL2_Type w__5))
              else (pure (())))))


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
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__CPTR_EL3_TCPAC == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
                  then
                    (do
                      let w__13 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__13 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CPTR_EL2 (Mk_CPTR_EL2_Type w__14))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CPTR_EL2 (Mk_CPTR_EL2_Type w__15))
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
                  let w__13 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGWTR_EL2_CSSELR_EL1 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__13 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CSSELR_EL1 (Mk_CSSELR_EL1_Type w__14)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg CSSELR_EL1 (Mk_CSSELR_EL1_Type w__15))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CSSELR_EL1 (Mk_CSSELR_EL1_Type w__16))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DACR32_EL2_SysRegWrite_94b89018206732e0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((! (HaveAArch32EL EL1)) : Bool)
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
                  let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg DACR32_EL2 (Mk_DACR32_EL2_Type w__4))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg DACR32_EL2 (Mk_DACR32_EL2_Type w__5))
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
              let w__19 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__19 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__24 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGWTR_EL2_DBGBCRn_EL1 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__28 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__26 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__27 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__26) +++ (_get_MDCR_EL2_Type_TDA
                                    w__27)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__28 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__30 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__34 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__31 ← (( do readReg OSLSR_EL1 ) : SailM
                                             (BitVec 64) )
                                           (pure ((((_get_OSLSR_EL1_Type_OSLK w__31) == 0#1) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaltingAllowed ()))
                                      else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__34 : Bool)
                              then
                                (do
                                  (Halt DebugHalt_SoftwareAccess))
                              else
                                (do
                                  let w__35 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) :
                                    SailM Bool )
                                  if (w__35 : Bool)
                                  then
                                    (do
                                      let w__36 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__37 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                        (BitVec 2) )
                                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg DBGBCR_EL1 (vectorUpdate w__36
                                        (Sail.Int.toNatChecked ((6 +i ((BitVec.toNat w__37) *i 16))))
                                        (Mk_DBGBCR_EL1_Type w__38)))
                                  else
                                    (do
                                      let w__39 ← (( do readReg DBGBCR_EL1 ) : SailM
                                        (Vector (BitVec 64) 64) )
                                      let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg DBGBCR_EL1 (vectorUpdate w__39 6
                                        (Mk_DBGBCR_EL1_Type w__40)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__46 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__46 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          let w__48 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__48 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__52 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__49 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                       (pure ((((_get_OSLSR_EL1_Type_OSLK w__49) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__52 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__53 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM
                                Bool )
                              if (w__53 : Bool)
                              then
                                (do
                                  let w__54 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__55 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM
                                    (BitVec 2) )
                                  let w__56 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg DBGBCR_EL1 (vectorUpdate w__54
                                    (Sail.Int.toNatChecked ((6 +i ((BitVec.toNat w__55) *i 16))))
                                    (Mk_DBGBCR_EL1_Type w__56)))
                              else
                                (do
                                  let w__57 ← (( do readReg DBGBCR_EL1 ) : SailM
                                    (Vector (BitVec 64) 64) )
                                  let w__58 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg DBGBCR_EL1 (vectorUpdate w__57 6
                                    (Mk_DBGBCR_EL1_Type w__58)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__62 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__59 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
                                   (pure ((((_get_OSLSR_EL1_Type_OSLK w__59) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__62 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__63 ← (( do (IsFeatureImplemented FEAT_Debugv8p9) ) : SailM Bool )
                          if (w__63 : Bool)
                          then
                            (do
                              let w__64 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__65 ← (( do (EffectiveMDSELR_EL1_BANK ()) ) : SailM (BitVec 2)
                                )
                              let w__66 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg DBGBCR_EL1 (vectorUpdate w__64
                                (Sail.Int.toNatChecked ((6 +i ((BitVec.toNat w__65) *i 16))))
                                (Mk_DBGBCR_EL1_Type w__66)))
                          else
                            (do
                              let w__67 ← (( do readReg DBGBCR_EL1 ) : SailM
                                (Vector (BitVec 64) 64) )
                              let w__68 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg DBGBCR_EL1 (vectorUpdate w__67 6 (Mk_DBGBCR_EL1_Type w__68)))))
                  else (pure (()))))))


end ArmFull.Functions
