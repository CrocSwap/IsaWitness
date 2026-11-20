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
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0053
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0083
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0141
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0252
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
def AMCR_SysRegRead32_3740e4968cc5855a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__1)
  let w__2 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __AMUSERENR_EL0_EN : (BitVec 1) := (_get_AMUSERENR_EL0_Type_EN w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do (AMUSERENR_read ()) ) : SailM (BitVec 32) )
  let __AMUSERENR_EN : (BitVec 1) := (_get_AMUSERENR_Type_EN w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__5)
  let w__6 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__6)
  let w__7 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__7)
  let w__8 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TAM : (BitVec 1) := (_get_CPTR_EL2_Type_TAM w__8)
  let w__9 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  let __HCPTR_TAM : (BitVec 1) := (_get_HCPTR_Type_TAM w__9)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__19 ← (( do
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
                            let w__13 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__13) == 1#1) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                   else (pure false)) : Bool)
              then
                (do
                  let w__17 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  (pure (((! w__17) : Bool))))
              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
      if (w__19 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__21 ← (( do
            (pure ((← do
                  let w__20 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                  (pure (((! w__20) : Bool)))) && ((__AMUSERENR_EL0_EN == 0#1) : Bool))) ) : SailM
            Bool )
          if (w__21 : Bool)
          then
            (do
              let w__25 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__23 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__23) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__25 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
          else
            (do
              let w__27 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__AMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
              if (w__27 : Bool)
              then
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__29 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__29) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__35 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__35 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__42 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__37 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__37) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__39) +++ (_get_HCR_EL2_Type_TGE
                                      w__40)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
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
                                  else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
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
                                      else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) :
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
                                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) )
                                    : SailM Bool )
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
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      let w__62 ← (( do (AMCR_read ()) ) : SailM (BitVec 32) )
                                      (R_set t (__get_AMCR w__62)))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__72 ← (( do
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
                                let w__66 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__66) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__70 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__70) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__72 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__76 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__74 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__74) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
              if (w__76 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__80 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__80 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__84 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__82 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__82) : Bool))))
                              else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__84 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__88 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__88 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__92 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__90 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__90) : Bool))))
                                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__92 : Bool)
                              then
                                (do
                                  let w__95 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__94 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__94) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__95 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  let w__96 ← (( do (AMCR_read ()) ) : SailM (BitVec 32) )
                                  (R_set t (__get_AMCR w__96)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__106 ← (( do
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
                                    let w__100 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__100) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__104 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__104) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__106 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__110 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__108 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__108) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__110 : Bool)
                  then
                    (do
                      let w__113 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__112 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__112) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__113 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                  else
                    (do
                      let w__114 ← (( do (AMCR_read ()) ) : SailM (BitVec 32) )
                      (R_set t (__get_AMCR w__114)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__115 ← (( do (AMCR_read ()) ) : SailM (BitVec 32) )
                  (R_set t (__get_AMCR w__115)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER0_SysRegRead32_2bb2f6721c44cef6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__1)
  let w__2 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __AMUSERENR_EL0_EN : (BitVec 1) := (_get_AMUSERENR_EL0_Type_EN w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do (AMUSERENR_read ()) ) : SailM (BitVec 32) )
  let __AMUSERENR_EN : (BitVec 1) := (_get_AMUSERENR_Type_EN w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__5)
  let w__6 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__6)
  let w__7 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__7)
  let w__8 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TAM : (BitVec 1) := (_get_CPTR_EL2_Type_TAM w__8)
  let w__9 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  let __HCPTR_TAM : (BitVec 1) := (_get_HCPTR_Type_TAM w__9)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__19 ← (( do
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
                            let w__13 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__13) == 1#1) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                   else (pure false)) : Bool)
              then
                (do
                  let w__17 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  (pure (((! w__17) : Bool))))
              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
      if (w__19 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__21 ← (( do
            (pure ((← do
                  let w__20 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                  (pure (((! w__20) : Bool)))) && ((__AMUSERENR_EL0_EN == 0#1) : Bool))) ) : SailM
            Bool )
          if (w__21 : Bool)
          then
            (do
              let w__25 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__23 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__23) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__25 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
          else
            (do
              let w__27 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__AMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
              if (w__27 : Bool)
              then
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__29 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__29) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__35 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__35 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__42 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__37 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__37) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__39) +++ (_get_HCR_EL2_Type_TGE
                                      w__40)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
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
                                  else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
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
                                      else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) :
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
                                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) )
                                    : SailM Bool )
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
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      let w__62 ← (( do (AMEVTYPER0_read 1) ) : SailM (BitVec 32)
                                        )
                                      (R_set t (__get_AMEVTYPER0 w__62)))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__72 ← (( do
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
                                let w__66 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__66) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__70 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__70) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__72 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__76 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__74 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__74) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
              if (w__76 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__80 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__80 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__84 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__82 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__82) : Bool))))
                              else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__84 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__88 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__88 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__92 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__90 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__90) : Bool))))
                                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__92 : Bool)
                              then
                                (do
                                  let w__95 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__94 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__94) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__95 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  let w__96 ← (( do (AMEVTYPER0_read 1) ) : SailM (BitVec 32) )
                                  (R_set t (__get_AMEVTYPER0 w__96)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__106 ← (( do
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
                                    let w__100 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__100) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__104 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__104) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__106 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__110 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__108 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__108) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__110 : Bool)
                  then
                    (do
                      let w__113 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__112 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__112) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__113 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                  else
                    (do
                      let w__114 ← (( do (AMEVTYPER0_read 1) ) : SailM (BitVec 32) )
                      (R_set t (__get_AMEVTYPER0 w__114)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__115 ← (( do (AMEVTYPER0_read 1) ) : SailM (BitVec 32) )
                  (R_set t (__get_AMEVTYPER0 w__115)))
              else (pure (())))))


end ArmFull.Functions
