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
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0053
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0066
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
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
      let w__21 ← (( do
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
                            let w__15 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__15) == 1#1) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                   else (pure false)) : Bool)
              then
                (do
                  let w__19 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  (pure (((! w__19) : Bool))))
              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
      if (w__21 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__23 ← (( do
            (pure ((← do
                  let w__22 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                  (pure (((! w__22) : Bool)))) && ((__AMUSERENR_EL0_EN == 0#1) : Bool))) ) : SailM
            Bool )
          if (w__23 : Bool)
          then
            (do
              let w__27 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__25 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__25) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__27 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
          else
            (do
              let w__29 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__AMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
              if (w__29 : Bool)
              then
                (do
                  let w__33 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__31 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__31) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__33 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__37 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__37 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__45 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     if ((← do
                                          (EL2Enabled ())) : Bool)
                                     then
                                       (do
                                         let w__39 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                         (pure (((! w__39) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__41) +++ (_get_HCR_EL2_Type_TGE
                                            w__42)) != 0b11#2) : Bool))))
                                else (pure false)) && ((3 <b 8) : Bool)))) && ((__HSTR_EL2_T0 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__45 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__50 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        (ELUsingAArch32 EL2))
                                    else (pure false)) && ((3 <b 8) : Bool)))) && ((__HSTR_T0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__50 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__52 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__52) : Bool))))
                                  else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__54 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__58 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__58 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__70 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               if ((← do
                                                    if ((← do
                                                         if ((← do
                                                              (EL2Enabled ())) : Bool)
                                                         then
                                                           (do
                                                             let w__60 ← (( do
                                                               (ELUsingAArch32 EL1) ) : SailM Bool )
                                                             (pure (((! w__60) : Bool))))
                                                         else (pure false)) : Bool)
                                                    then
                                                      (do
                                                        let w__62 ← (( do readReg HCR_EL2 ) :
                                                          SailM (BitVec 64) )
                                                        let w__63 ← (( do readReg HCR_EL2 ) :
                                                          SailM (BitVec 64) )
                                                        (pure (((((_get_HCR_EL2_Type_E2H w__62) +++ (_get_HCR_EL2_Type_TGE
                                                                w__63)) != 0b11#2) : Bool))))
                                                    else (pure false)) : Bool)
                                               then
                                                 (do
                                                   (IsFeatureImplemented FEAT_FGT))
                                               else (pure false)) : Bool)
                                          then
                                            (do
                                              (pure ((← do
                                                    let w__67 ← (( do (HaveEL EL3) ) : SailM Bool
                                                      )
                                                    (pure (((! w__67) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                                          else (pure false)) && ((__HAFGRTR_EL2_AMEVCNTR03_EL0 == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__70 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      let w__74 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__72 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__72) : Bool))))
                                              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__74 : Bool)
                                      then
                                        (do
                                          let w__77 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__76 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__76) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__77 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x04#8))))
                                      else
                                        (do
                                          let w__78 ← (( do readReg AMEVCNTR0 ) : SailM
                                            (Vector (BitVec 64) 4) )
                                          let w__79 ← (( do readReg AMEVCNTR0 ) : SailM
                                            (Vector (BitVec 64) 4) )
                                          let (__tup_0, __tup_1) :=
                                            ((Sail.BitVec.extractLsb (GetElem?.getElem! w__78 3) 63
                                              32), (Sail.BitVec.extractLsb
                                              (GetElem?.getElem! w__79 3) 31 0))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1)))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__89 ← (( do
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
                                let w__83 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__83) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__87 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__87) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__89 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__94 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__91 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__91) : Bool))))
                            else (pure false)) && ((3 <b 8) : Bool)))) && ((__HSTR_EL2_T0 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__94 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__99 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (ELUsingAArch32 EL2))
                                else (pure false)) && ((3 <b 8) : Bool)))) && ((__HSTR_T0 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__99 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__103 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__101 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__101) : Bool))))
                              else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__103 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__107 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__107 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__111 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__109 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__109) : Bool))))
                                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__111 : Bool)
                              then
                                (do
                                  let w__114 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__113 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__113) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__114 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                              else
                                (do
                                  let w__115 ← (( do readReg AMEVCNTR0 ) : SailM
                                    (Vector (BitVec 64) 4) )
                                  let w__116 ← (( do readReg AMEVCNTR0 ) : SailM
                                    (Vector (BitVec 64) 4) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb (GetElem?.getElem! w__115 3) 63 32), (Sail.BitVec.extractLsb
                                      (GetElem?.getElem! w__116 3) 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__126 ← (( do
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
                                    let w__120 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__120) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__124 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__124) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__126 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__130 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__128 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__128) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__130 : Bool)
                  then
                    (do
                      let w__133 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__132 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__132) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__133 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                  else
                    (do
                      let w__134 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                      let w__135 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb (GetElem?.getElem! w__134 3) 63 32), (Sail.BitVec.extractLsb
                          (GetElem?.getElem! w__135 3) 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__136 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                  let w__137 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb (GetElem?.getElem! w__136 3) 63 32), (Sail.BitVec.extractLsb
                      (GetElem?.getElem! w__137 3) 31 0))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegRead64_66e81afe82d2c192 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
  let __HAFGRTR_EL2_AMEVCNTR01_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR01_EL0 w__11)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__21 ← (( do
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
                            let w__15 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__15) == 1#1) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                   else (pure false)) : Bool)
              then
                (do
                  let w__19 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  (pure (((! w__19) : Bool))))
              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
      if (w__21 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__23 ← (( do
            (pure ((← do
                  let w__22 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                  (pure (((! w__22) : Bool)))) && ((__AMUSERENR_EL0_EN == 0#1) : Bool))) ) : SailM
            Bool )
          if (w__23 : Bool)
          then
            (do
              let w__27 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__25 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__25) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__27 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
          else
            (do
              let w__29 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__AMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
              if (w__29 : Bool)
              then
                (do
                  let w__33 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__31 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__31) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__33 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__37 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__37 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__45 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     if ((← do
                                          (EL2Enabled ())) : Bool)
                                     then
                                       (do
                                         let w__39 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                         (pure (((! w__39) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__41) +++ (_get_HCR_EL2_Type_TGE
                                            w__42)) != 0b11#2) : Bool))))
                                else (pure false)) && ((1 <b 8) : Bool)))) && ((__HSTR_EL2_T0 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__45 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__50 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        (ELUsingAArch32 EL2))
                                    else (pure false)) && ((1 <b 8) : Bool)))) && ((__HSTR_T0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__50 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__52 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__52) : Bool))))
                                  else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__54 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__58 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__58 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__70 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               if ((← do
                                                    if ((← do
                                                         if ((← do
                                                              (EL2Enabled ())) : Bool)
                                                         then
                                                           (do
                                                             let w__60 ← (( do
                                                               (ELUsingAArch32 EL1) ) : SailM Bool )
                                                             (pure (((! w__60) : Bool))))
                                                         else (pure false)) : Bool)
                                                    then
                                                      (do
                                                        let w__62 ← (( do readReg HCR_EL2 ) :
                                                          SailM (BitVec 64) )
                                                        let w__63 ← (( do readReg HCR_EL2 ) :
                                                          SailM (BitVec 64) )
                                                        (pure (((((_get_HCR_EL2_Type_E2H w__62) +++ (_get_HCR_EL2_Type_TGE
                                                                w__63)) != 0b11#2) : Bool))))
                                                    else (pure false)) : Bool)
                                               then
                                                 (do
                                                   (IsFeatureImplemented FEAT_FGT))
                                               else (pure false)) : Bool)
                                          then
                                            (do
                                              (pure ((← do
                                                    let w__67 ← (( do (HaveEL EL3) ) : SailM Bool
                                                      )
                                                    (pure (((! w__67) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                                          else (pure false)) && ((__HAFGRTR_EL2_AMEVCNTR01_EL0 == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__70 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      let w__74 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__72 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__72) : Bool))))
                                              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__74 : Bool)
                                      then
                                        (do
                                          let w__77 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__76 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__76) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__77 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x04#8))))
                                      else
                                        (do
                                          let w__78 ← (( do readReg AMEVCNTR0 ) : SailM
                                            (Vector (BitVec 64) 4) )
                                          let w__79 ← (( do readReg AMEVCNTR0 ) : SailM
                                            (Vector (BitVec 64) 4) )
                                          let (__tup_0, __tup_1) :=
                                            ((Sail.BitVec.extractLsb (GetElem?.getElem! w__78 1) 63
                                              32), (Sail.BitVec.extractLsb
                                              (GetElem?.getElem! w__79 1) 31 0))
                                          (R_set t2 __tup_0)
                                          (R_set t __tup_1)))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__89 ← (( do
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
                                let w__83 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__83) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__87 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__87) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__89 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__94 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__91 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__91) : Bool))))
                            else (pure false)) && ((1 <b 8) : Bool)))) && ((__HSTR_EL2_T0 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__94 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__99 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (ELUsingAArch32 EL2))
                                else (pure false)) && ((1 <b 8) : Bool)))) && ((__HSTR_T0 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__99 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__103 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__101 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__101) : Bool))))
                              else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__103 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__107 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__107 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__111 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__109 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__109) : Bool))))
                                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__111 : Bool)
                              then
                                (do
                                  let w__114 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__113 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__113) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__114 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                              else
                                (do
                                  let w__115 ← (( do readReg AMEVCNTR0 ) : SailM
                                    (Vector (BitVec 64) 4) )
                                  let w__116 ← (( do readReg AMEVCNTR0 ) : SailM
                                    (Vector (BitVec 64) 4) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb (GetElem?.getElem! w__115 1) 63 32), (Sail.BitVec.extractLsb
                                      (GetElem?.getElem! w__116 1) 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__126 ← (( do
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
                                    let w__120 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__120) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__124 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__124) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__126 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__130 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__128 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__128) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__130 : Bool)
                  then
                    (do
                      let w__133 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__132 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__132) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__133 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                  else
                    (do
                      let w__134 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                      let w__135 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb (GetElem?.getElem! w__134 1) 63 32), (Sail.BitVec.extractLsb
                          (GetElem?.getElem! w__135 1) 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__136 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                  let w__137 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb (GetElem?.getElem! w__136 1) 63 32), (Sail.BitVec.extractLsb
                      (GetElem?.getElem! w__137 1) 31 0))
                  (R_set t2 __tup_0)
                  (R_set t __tup_1))
              else (pure (())))))


end ArmFull.Functions
