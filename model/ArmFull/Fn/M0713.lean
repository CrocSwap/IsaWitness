import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0047
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0059
import ArmFull.Fn.M0066
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0203
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

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegRead64_2b274c768298c3f9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__6)
  let w__7 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__7)
  let w__8 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TAM : (BitVec 1) := (_get_CPTR_EL2_Type_TAM w__8)
  let w__9 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  let __HCPTR_TAM : (BitVec 1) := (_get_HCPTR_Type_TAM w__9)
  let w__10 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__10)
  let w__11 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HAFGRTR_EL2_AMEVCNTR00_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR00_EL0 w__11)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__20 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        if ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                        then
                          (do
                            let w__14 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__14) == 1#1) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                   else (pure false)) : Bool)
              then
                (do
                  let w__18 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  (pure (((! w__18) : Bool))))
              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
      if (w__20 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__22 ← (( do
            (pure ((← do
                  let w__21 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                  (pure (((! w__21) : Bool)))) && ((__AMUSERENR_EL0_EN == 0#1) : Bool))) ) : SailM
            Bool )
          if (w__22 : Bool)
          then
            (do
              let w__26 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__24 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__24) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
          else
            (do
              let w__28 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__AMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then
                (do
                  let w__32 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__30 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__30) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__32 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__36 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     if ((← do
                                          (EL2Enabled ())) : Bool)
                                     then
                                       (do
                                         let w__38 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                         (pure (((! w__38) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__40) +++ (_get_HCR_EL2_Type_TGE
                                            w__41)) != 0b11#2) : Bool))))
                                else (pure false)) && ((0 <b 8) : Bool)))) && ((__HSTR_EL2_T0 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__44 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__49 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        (ELUsingAArch32 EL2))
                                    else (pure false)) && ((0 <b 8) : Bool)))) && ((__HSTR_T0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__49 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__53 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__51 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__51) : Bool))))
                                  else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__53 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__57 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__57 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__67 ← (( do
                                    (pure ((← do
                                          (pure ((← do
                                                if ((← do
                                                     if ((← do
                                                          if ((← do
                                                               (EL2Enabled ())) : Bool)
                                                          then
                                                            (do
                                                              let w__59 ← (( do
                                                                (ELUsingAArch32 EL1) ) : SailM Bool
                                                                )
                                                              (pure (((! w__59) : Bool))))
                                                          else (pure false)) : Bool)
                                                     then
                                                       (do
                                                         let w__61 ← (( do readReg HCR_EL2 ) :
                                                           SailM (BitVec 64) )
                                                         let w__62 ← (( do readReg HCR_EL2 ) :
                                                           SailM (BitVec 64) )
                                                         (pure (((((_get_HCR_EL2_Type_E2H w__61) +++ (_get_HCR_EL2_Type_TGE
                                                                 w__62)) != 0b11#2) : Bool))))
                                                     else (pure false)) : Bool)
                                                then
                                                  (do
                                                    (IsFeatureImplemented FEAT_FGT))
                                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HAFGRTR_EL2_AMEVCNTR00_EL0 == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__67 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      let w__70 ← (( do
                                        (pure ((← do
                                              if (((HaveEL EL3) : Bool) : Bool)
                                              then
                                                (do
                                                  let w__68 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__68) : Bool))))
                                              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__70 : Bool)
                                      then
                                        (do
                                          let w__73 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__72 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__72) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__73 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x04#8))))
                                      else
                                        (do
                                          let w__74 ← (( do readReg AMEVCNTR0 ) : SailM
                                            (Vector (BitVec 64) 4) )
                                          let w__75 ← (( do readReg AMEVCNTR0 ) : SailM
                                            (Vector (BitVec 64) 4) )
                                          let (__tup_0, __tup_1) :=
                                            ((Sail.BitVec.extractLsb (GetElem?.getElem! w__74 0) 63
                                              32), (Sail.BitVec.extractLsb
                                              (GetElem?.getElem! w__75 0) 31 0))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1)))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__84 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__78 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__78) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__82 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__82) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__84 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__89 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__86 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__86) : Bool))))
                            else (pure false)) && ((0 <b 8) : Bool)))) && ((__HSTR_EL2_T0 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__89 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__94 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (ELUsingAArch32 EL2))
                                else (pure false)) && ((0 <b 8) : Bool)))) && ((__HSTR_T0 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__94 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__98 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__96 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__96) : Bool))))
                              else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__98 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__102 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__102 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__105 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          let w__103 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__103) : Bool))))
                                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__105 : Bool)
                              then
                                (do
                                  let w__108 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__107 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__107) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__108 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                              else
                                (do
                                  let w__109 ← (( do readReg AMEVCNTR0 ) : SailM
                                    (Vector (BitVec 64) 4) )
                                  let w__110 ← (( do readReg AMEVCNTR0 ) : SailM
                                    (Vector (BitVec 64) 4) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb (GetElem?.getElem! w__109 0) 63 32), (Sail.BitVec.extractLsb
                                      (GetElem?.getElem! w__110 0) 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__119 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__113 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__113) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__117 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__117) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__119 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__122 ← (( do
                    (pure ((← do
                          if (((HaveEL EL3) : Bool) : Bool)
                          then
                            (do
                              let w__120 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__120) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__122 : Bool)
                  then
                    (do
                      let w__125 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__124 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__124) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__125 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                  else
                    (do
                      let w__126 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                      let w__127 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb (GetElem?.getElem! w__126 0) 63 32), (Sail.BitVec.extractLsb
                          (GetElem?.getElem! w__127 0) 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__128 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                  let w__129 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb (GetElem?.getElem! w__128 0) 63 32), (Sail.BitVec.extractLsb
                      (GetElem?.getElem! w__129 0) 31 0))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegRead64_58cd2445e81e8975 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__6)
  let w__7 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__7)
  let w__8 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TAM : (BitVec 1) := (_get_CPTR_EL2_Type_TAM w__8)
  let w__9 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  let __HCPTR_TAM : (BitVec 1) := (_get_HCPTR_Type_TAM w__9)
  let w__10 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__10)
  let w__11 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HAFGRTR_EL2_AMEVCNTR03_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR03_EL0 w__11)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__20 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        if ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                        then
                          (do
                            let w__14 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__14) == 1#1) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                   else (pure false)) : Bool)
              then
                (do
                  let w__18 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  (pure (((! w__18) : Bool))))
              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
      if (w__20 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__22 ← (( do
            (pure ((← do
                  let w__21 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                  (pure (((! w__21) : Bool)))) && ((__AMUSERENR_EL0_EN == 0#1) : Bool))) ) : SailM
            Bool )
          if (w__22 : Bool)
          then
            (do
              let w__26 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__24 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__24) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
          else
            (do
              let w__28 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__AMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then
                (do
                  let w__32 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__30 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__30) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__32 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__36 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     if ((← do
                                          (EL2Enabled ())) : Bool)
                                     then
                                       (do
                                         let w__38 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                         (pure (((! w__38) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__40) +++ (_get_HCR_EL2_Type_TGE
                                            w__41)) != 0b11#2) : Bool))))
                                else (pure false)) && ((3 <b 8) : Bool)))) && ((__HSTR_EL2_T0 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__44 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__49 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        (ELUsingAArch32 EL2))
                                    else (pure false)) && ((3 <b 8) : Bool)))) && ((__HSTR_T0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__49 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__53 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__51 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__51) : Bool))))
                                  else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__53 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__57 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__57 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__67 ← (( do
                                    (pure ((← do
                                          (pure ((← do
                                                if ((← do
                                                     if ((← do
                                                          if ((← do
                                                               (EL2Enabled ())) : Bool)
                                                          then
                                                            (do
                                                              let w__59 ← (( do
                                                                (ELUsingAArch32 EL1) ) : SailM Bool
                                                                )
                                                              (pure (((! w__59) : Bool))))
                                                          else (pure false)) : Bool)
                                                     then
                                                       (do
                                                         let w__61 ← (( do readReg HCR_EL2 ) :
                                                           SailM (BitVec 64) )
                                                         let w__62 ← (( do readReg HCR_EL2 ) :
                                                           SailM (BitVec 64) )
                                                         (pure (((((_get_HCR_EL2_Type_E2H w__61) +++ (_get_HCR_EL2_Type_TGE
                                                                 w__62)) != 0b11#2) : Bool))))
                                                     else (pure false)) : Bool)
                                                then
                                                  (do
                                                    (IsFeatureImplemented FEAT_FGT))
                                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HAFGRTR_EL2_AMEVCNTR03_EL0 == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__67 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      let w__70 ← (( do
                                        (pure ((← do
                                              if (((HaveEL EL3) : Bool) : Bool)
                                              then
                                                (do
                                                  let w__68 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__68) : Bool))))
                                              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__70 : Bool)
                                      then
                                        (do
                                          let w__73 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__72 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__72) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__73 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x04#8))))
                                      else
                                        (do
                                          let w__74 ← (( do readReg AMEVCNTR0 ) : SailM
                                            (Vector (BitVec 64) 4) )
                                          let w__75 ← (( do readReg AMEVCNTR0 ) : SailM
                                            (Vector (BitVec 64) 4) )
                                          let (__tup_0, __tup_1) :=
                                            ((Sail.BitVec.extractLsb (GetElem?.getElem! w__74 3) 63
                                              32), (Sail.BitVec.extractLsb
                                              (GetElem?.getElem! w__75 3) 31 0))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1)))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__84 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__78 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__78) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__82 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__82) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__84 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__89 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__86 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__86) : Bool))))
                            else (pure false)) && ((3 <b 8) : Bool)))) && ((__HSTR_EL2_T0 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__89 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__94 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (ELUsingAArch32 EL2))
                                else (pure false)) && ((3 <b 8) : Bool)))) && ((__HSTR_T0 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__94 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__98 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__96 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__96) : Bool))))
                              else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__98 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__102 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__102 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__105 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          let w__103 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__103) : Bool))))
                                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__105 : Bool)
                              then
                                (do
                                  let w__108 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__107 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__107) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__108 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                              else
                                (do
                                  let w__109 ← (( do readReg AMEVCNTR0 ) : SailM
                                    (Vector (BitVec 64) 4) )
                                  let w__110 ← (( do readReg AMEVCNTR0 ) : SailM
                                    (Vector (BitVec 64) 4) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb (GetElem?.getElem! w__109 3) 63 32), (Sail.BitVec.extractLsb
                                      (GetElem?.getElem! w__110 3) 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__119 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__113 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__113) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__117 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__117) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__119 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__122 ← (( do
                    (pure ((← do
                          if (((HaveEL EL3) : Bool) : Bool)
                          then
                            (do
                              let w__120 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__120) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__122 : Bool)
                  then
                    (do
                      let w__125 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__124 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__124) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__125 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                  else
                    (do
                      let w__126 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                      let w__127 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb (GetElem?.getElem! w__126 3) 63 32), (Sail.BitVec.extractLsb
                          (GetElem?.getElem! w__127 3) 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__128 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                  let w__129 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb (GetElem?.getElem! w__128 3) 63 32), (Sail.BitVec.extractLsb
                      (GetElem?.getElem! w__129 3) 31 0))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure (())))))


end ArmFull.Functions
