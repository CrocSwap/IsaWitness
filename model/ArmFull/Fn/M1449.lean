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
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0144
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
def SMCR_EL1_SysRegRead_924df8670c1f630f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_ESM : (BitVec 1) := (_get_CPTR_EL3_Type_ESM w__2)
  let w__3 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  let __CPACR_EL1_SMEN : (BitVec 2) := (_get_CPACR_EL1_Type_SMEN w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TSM : (BitVec 1) := (_get_CPTR_EL2_Type_TSM w__5)
  let w__6 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_SMEN : (BitVec 2) := (_get_CPTR_EL2_Type_SMEN w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
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
                  else (pure false)) && ((__CPTR_EL3_ESM == 0#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((let b__2 := __CPACR_EL1_SMEN
                 (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 0 0)) == (0#1 : (BitVec 1))) : Bool)
                 then true
                 else false : Bool)) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x1D#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          (pure ((← do
                                (EL2Enabled ())) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CPTR_EL2_TSM == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
                  else
                    (do
                      let w__19 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (EL2Enabled ())) && ((__HCR_EL2_E2H == 1#1) : Bool)))) && (let b__1 :=
                              __CPTR_EL2_SMEN
                            (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
                            then true
                            else false : Bool)))) ) : SailM Bool )
                      if (w__19 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
                      else
                        (do
                          let w__21 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_ESM == 0#1) : Bool))) ) : SailM Bool
                            )
                          if (w__21 : Bool)
                          then
                            (do
                              let w__23 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__23 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))))
                          else
                            (do
                              let w__28 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_NV2 w__25) +++ ((_get_HCR_EL2_Type_NV1
                                              w__26) +++ (_get_HCR_EL2_Type_NV w__27))) == 0b111#3) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__28 : Bool)
                              then
                                (do
                                  let w__29 ← (( do (NVMem_read (BitVec.toNat 0x1F0#12)) ) : SailM
                                    (BitVec 64) )
                                  (X_set t 64 w__29))
                              else
                                (do
                                  let w__30 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
                                  (X_set t 64 (__get_SMCR_EL1 w__30)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__37 ← (( do
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
                      else (pure false)) && ((__CPTR_EL3_ESM == 0#1) : Bool))) ) : SailM Bool )
              if (w__37 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TSM == 1#1)) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_SMEN
                           (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool))) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
                      else
                        (do
                          let w__39 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_ESM == 0#1) : Bool))) ) : SailM Bool
                            )
                          if (w__39 : Bool)
                          then
                            (do
                              let w__41 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__41 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))))
                          else
                            (do
                              if ((__HCR_EL2_E2H == 1#1) : Bool)
                              then
                                (do
                                  let w__42 ← (( do readReg SMCR_EL2 ) : SailM (BitVec 64) )
                                  (X_set t 64 (__get_SMCR_EL2 w__42)))
                              else
                                (do
                                  let w__43 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
                                  (X_set t 64 (__get_SMCR_EL1 w__43))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8)))
                  else
                    (do
                      let w__44 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_SMCR_EL1 w__44))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SMCR_EL1_SysRegRead_ea88aa9e02fbf3b4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  let w__4 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_ESM : (BitVec 1) := (_get_CPTR_EL3_Type_ESM w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_SMEN : (BitVec 2) := (_get_CPTR_EL2_Type_SMEN w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__7) +++ ((_get_HCR_EL2_Type_NV1 w__8) +++ (_get_HCR_EL2_Type_NV
                          w__9))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__10 : Bool)
          then
            (do
              let w__11 ← (( do (NVMem_read (BitVec.toNat 0x1F0#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__11))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
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
                          else (pure false)) && ((__CPTR_EL3_ESM == 0#1) : Bool))) ) : SailM Bool )
                  if (w__20 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((let b__0 := __CPTR_EL2_SMEN
                         (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                         then true
                         else false : Bool)) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
                      else
                        (do
                          let w__22 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_ESM == 0#1) : Bool))) ) : SailM Bool
                            )
                          if (w__22 : Bool)
                          then
                            (do
                              let w__24 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__24 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))))
                          else
                            (do
                              let w__25 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_SMCR_EL1 w__25))))))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__27 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__27) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      if ((__CPTR_EL3_ESM == 0#1) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8)))
                      else
                        (do
                          let w__30 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_SMCR_EL1 w__30))))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SMPRIMAP_EL2_SysRegRead_c09b27037a76a5c0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_ESM : (BitVec 1) := (_get_CPTR_EL3_Type_ESM w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__5) +++ (_get_HCR_EL2_Type_NV w__6)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let w__8 ← (( do (NVMem_read (BitVec.toNat 0x1F8#12)) ) : SailM (BitVec 64) )
              (X_set t 64 w__8))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__17 ← (( do
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
                      else (pure false)) && ((__CPTR_EL3_ESM == 0#1) : Bool))) ) : SailM Bool )
              if (w__17 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__CPTR_EL3_ESM == 0#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__22 ← (( do readReg SMPRIMAP_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 w__22))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__23 ← (( do readReg SMPRIMAP_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 w__23)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPMACCESSR_EL1_SysRegRead_26644746ac7f02e9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_EnPM2 : (BitVec 1) := (_get_MDCR_EL3_Type_EnPM2 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__3)
  let w__4 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR2_EL2_nSPMACCESSR_EL1 : (BitVec 1) := (_get_HDFGRTR2_EL2_Type_nSPMACCESSR_EL1 w__4)
  let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_EnSPM : (BitVec 1) := (_get_MDCR_EL2_Type_EnSPM w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
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
                  else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
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
                               (IsFeatureImplemented FEAT_FGT2))
                           else (pure false)) : Bool)
                      then
                        (do
                          (HaveEL EL3))
                      else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__19 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__23 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HDFGRTR2_EL2_nSPMACCESSR_EL1 == 0#1) : Bool))) )
                    : SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__25 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__25 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__27 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__27 : Bool)
                          then
                            (do
                              let w__29 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__29 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__34 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_NV2 w__31) +++ ((_get_HCR_EL2_Type_NV1
                                              w__32) +++ (_get_HCR_EL2_Type_NV w__33))) == 0b111#3) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__34 : Bool)
                              then
                                (do
                                  let w__35 ← (( do (NVMem_read (BitVec.toNat 0x8E8#12)) ) : SailM
                                    (BitVec 64) )
                                  (X_set t 64 w__35))
                              else
                                (do
                                  let w__36 ← (( do readReg SPMACCESSR_EL1 ) : SailM (BitVec 64) )
                                  (X_set t 64 w__36))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__43 ← (( do
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
                      else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__43 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__45 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
                  if (w__45 : Bool)
                  then
                    (do
                      let w__47 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__47 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__48 ← (( do readReg SPMACCESSR_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64 w__48))
                      else
                        (do
                          let w__49 ← (( do readReg SPMACCESSR_EL1 ) : SailM (BitVec 64) )
                          (X_set t 64 w__49)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__50 ← (( do readReg SPMACCESSR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 w__50))
              else (pure (())))))


end ArmFull.Functions
