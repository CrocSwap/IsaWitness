module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0138
public import ArmFull.Fn.M0139
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0173
public import ArmFull.Fn.M0176
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
def ESR_EL1_SysRegRead_0503f2c5949dd1a4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__5 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__3) +++ (_get_HCR_EL2_Type_NV w__4)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__6 ← (( do readReg ESR_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ESR_EL1 w__6)))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg ESR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ESR_EL2 w__9)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg ESR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_ESR_EL2 w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def FAR_EL2_SysRegRead_49254d82e8554d12 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__5 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__3) +++ (_get_HCR_EL2_Type_NV w__4)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__6 ← (( do readReg FAR_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__6))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg FAR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 w__9))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg FAR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__10))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def FPCR_SysRegRead_48b824e8174adfc0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TFP : (BitVec 1) := (_get_CPTR_EL3_Type_TFP w__2)
  let w__3 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  let __CPACR_EL1_FPEN : (BitVec 2) := (_get_CPACR_EL1_Type_FPEN w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_FPEN : (BitVec 2) := (_get_CPTR_EL2_Type_FPEN w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__6)
  let w__7 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TFP : (BitVec 1) := (_get_CPTR_EL2_Type_TFP w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__14 ← (( do
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
              else (pure false)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool )
      if (w__14 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__19 ← (( do
            (pure ((← do
                  let w__18 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__16) +++ (_get_HCR_EL2_Type_TGE w__17)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__18) : Bool)))) && ((__CPACR_EL1_FPEN != 0b11#2) : Bool))) ) : SailM
            Bool )
          if (w__19 : Bool)
          then
            (do
              let w__21 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__21 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x00#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x07#8))))
          else
            (do
              let w__26 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__23) +++ (_get_HCR_EL2_Type_TGE w__24)) == 0b11#2) : Bool))))
                      else (pure false)) && ((__CPTR_EL2_FPEN != 0b11#2) : Bool))) ) : SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
              else
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          (pure ((← do
                                (EL2Enabled ())) && ((__HCR_EL2_E2H == 1#1) : Bool)))) && (let b__3 :=
                          __CPTR_EL2_FPEN
                        (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 0 0)) == (0#1 : (BitVec 1))) : Bool)
                        then true
                        else false : Bool)))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                  else
                    (do
                      let w__32 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (EL2Enabled ())) && ((__HCR_EL2_E2H != 1#1) : Bool)))) && ((__CPTR_EL2_TFP == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__32 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                      else
                        (do
                          let w__34 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__34 : Bool)
                          then
                            (do
                              let w__36 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__36 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))))
                          else
                            (do
                              let w__37 ← (( do readReg FPCR ) : SailM (BitVec 64) )
                              let w__38 ← (( do (__get_FPCR w__37) ) : SailM (BitVec 64) )
                              (X_set t 64 w__38))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__45 ← (( do
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
                  else (pure false)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool )
          if (w__45 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((let b__2 := __CPACR_EL1_FPEN
                 (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 0 0)) == (0#1 : (BitVec 1))) : Bool)
                 then true
                 else false : Bool)) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x07#8)))
              else
                (do
                  let w__48 ← (( do
                    (pure ((← do
                          (pure ((← do
                                (EL2Enabled ())) && ((__HCR_EL2_E2H != 1#1) : Bool)))) && ((__CPTR_EL2_TFP == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__48 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                  else
                    (do
                      let w__51 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (EL2Enabled ())) && ((__HCR_EL2_E2H == 1#1) : Bool)))) && (let b__1 :=
                              __CPTR_EL2_FPEN
                            (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
                            then true
                            else false : Bool)))) ) : SailM Bool )
                      if (w__51 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                      else
                        (do
                          let w__53 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__53 : Bool)
                          then
                            (do
                              let w__55 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__55 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))))
                          else
                            (do
                              let w__56 ← (( do readReg FPCR ) : SailM (BitVec 64) )
                              let w__57 ← (( do (__get_FPCR w__56) ) : SailM (BitVec 64) )
                              (X_set t 64 w__57)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__64 ← (( do
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
                      else (pure false)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool )
              if (w__64 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TFP == 1#1)) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_FPEN
                           (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool))) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                      else
                        (do
                          let w__66 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__66 : Bool)
                          then
                            (do
                              let w__68 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__68 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))))
                          else
                            (do
                              let w__69 ← (( do readReg FPCR ) : SailM (BitVec 64) )
                              let w__70 ← (( do (__get_FPCR w__69) ) : SailM (BitVec 64) )
                              (X_set t 64 w__70))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_TFP == 1#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8)))
                  else
                    (do
                      let w__71 ← (( do readReg FPCR ) : SailM (BitVec 64) )
                      let w__72 ← (( do (__get_FPCR w__71) ) : SailM (BitVec 64) )
                      (X_set t 64 w__72)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def FPEXC32_EL2_SysRegRead_0bed2a86b1b2240d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TFP : (BitVec 1) := (_get_CPTR_EL3_Type_TFP w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TFP : (BitVec 1) := (_get_CPTR_EL2_Type_TFP w__5)
  let w__6 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_FPEN : (BitVec 2) := (_get_CPTR_EL2_Type_FPEN w__6)
  let w__7 ← (( do (HaveAArch32EL EL1) ) : SailM Bool )
  if ((! w__7) : Bool)
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
              let w__9 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__16 ← (( do
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
                          else (pure false)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool )
                  if (w__16 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TFP == 1#1)) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                      else
                        (do
                          if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_FPEN
                               (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0
                                      0)) == (0#1 : (BitVec 1))) : Bool)
                               then true
                               else false : Bool))) : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                          else
                            (do
                              let w__18 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__18 : Bool)
                              then
                                (do
                                  let w__20 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__20 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))))
                              else
                                (do
                                  let w__21 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
                                  let w__22 ← (( do (__get_FPEXC32_EL2 w__21) ) : SailM
                                    (BitVec 64) )
                                  (X_set t 64 w__22))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if ((__CPTR_EL3_TFP == 1#1) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8)))
                      else
                        (do
                          let w__23 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
                          let w__24 ← (( do (__get_FPEXC32_EL2 w__23) ) : SailM (BitVec 64) )
                          (X_set t 64 w__24)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def FPSR_SysRegRead_f0c8f9b942affbc0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TFP : (BitVec 1) := (_get_CPTR_EL3_Type_TFP w__2)
  let w__3 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  let __CPACR_EL1_FPEN : (BitVec 2) := (_get_CPACR_EL1_Type_FPEN w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_FPEN : (BitVec 2) := (_get_CPTR_EL2_Type_FPEN w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__6)
  let w__7 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TFP : (BitVec 1) := (_get_CPTR_EL2_Type_TFP w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__14 ← (( do
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
              else (pure false)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool )
      if (w__14 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__19 ← (( do
            (pure ((← do
                  let w__18 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__16) +++ (_get_HCR_EL2_Type_TGE w__17)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__18) : Bool)))) && ((__CPACR_EL1_FPEN != 0b11#2) : Bool))) ) : SailM
            Bool )
          if (w__19 : Bool)
          then
            (do
              let w__21 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__21 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x00#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x07#8))))
          else
            (do
              let w__26 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__23) +++ (_get_HCR_EL2_Type_TGE w__24)) == 0b11#2) : Bool))))
                      else (pure false)) && ((__CPTR_EL2_FPEN != 0b11#2) : Bool))) ) : SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
              else
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          (pure ((← do
                                (EL2Enabled ())) && ((__HCR_EL2_E2H == 1#1) : Bool)))) && (let b__3 :=
                          __CPTR_EL2_FPEN
                        (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 0 0)) == (0#1 : (BitVec 1))) : Bool)
                        then true
                        else false : Bool)))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                  else
                    (do
                      let w__32 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (EL2Enabled ())) && ((__HCR_EL2_E2H != 1#1) : Bool)))) && ((__CPTR_EL2_TFP == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__32 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                      else
                        (do
                          let w__34 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__34 : Bool)
                          then
                            (do
                              let w__36 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__36 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))))
                          else
                            (do
                              let w__37 ← (( do readReg FPSR ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_FPSR w__37)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__44 ← (( do
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
                  else (pure false)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool )
          if (w__44 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((let b__2 := __CPACR_EL1_FPEN
                 (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 0 0)) == (0#1 : (BitVec 1))) : Bool)
                 then true
                 else false : Bool)) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x07#8)))
              else
                (do
                  let w__47 ← (( do
                    (pure ((← do
                          (pure ((← do
                                (EL2Enabled ())) && ((__HCR_EL2_E2H != 1#1) : Bool)))) && ((__CPTR_EL2_TFP == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__47 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                  else
                    (do
                      let w__50 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (EL2Enabled ())) && ((__HCR_EL2_E2H == 1#1) : Bool)))) && (let b__1 :=
                              __CPTR_EL2_FPEN
                            (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
                            then true
                            else false : Bool)))) ) : SailM Bool )
                      if (w__50 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                      else
                        (do
                          let w__52 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__52 : Bool)
                          then
                            (do
                              let w__54 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__54 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))))
                          else
                            (do
                              let w__55 ← (( do readReg FPSR ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_FPSR w__55))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__62 ← (( do
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
                      else (pure false)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool )
              if (w__62 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TFP == 1#1)) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_FPEN
                           (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool))) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x07#8)))
                      else
                        (do
                          let w__64 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TFP == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__64 : Bool)
                          then
                            (do
                              let w__66 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__66 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8))))
                          else
                            (do
                              let w__67 ← (( do readReg FPSR ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_FPSR w__67)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_TFP == 1#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x07#8)))
                  else
                    (do
                      let w__68 ← (( do readReg FPSR ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_FPSR w__68))))
              else (pure (())))))


end ArmFull.Functions
