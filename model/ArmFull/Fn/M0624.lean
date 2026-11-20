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
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0067
public import ArmFull.Fn.M0083
public import ArmFull.Fn.M0092
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
def AMEVTYPER1_SysRegRead32_b4ee1ae1a6a9e5fe (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__10 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__10)
  let w__11 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HAFGRTR_EL2_AMEVTYPER113_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVTYPER113_EL0 w__11)
  let w__12 ← (( do (IsG1ActivityMonitorImplemented 13) ) : SailM Bool )
  if ((! w__12) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__22 ← (( do
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
                                let w__16 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__16) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__20 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__20) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__22 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__24 ← (( do
                (pure ((← do
                      let w__23 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                      (pure (((! w__23) : Bool)))) && ((__AMUSERENR_EL0_EN == 0#1) : Bool))) ) :
                SailM Bool )
              if (w__24 : Bool)
              then
                (do
                  let w__28 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__26 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__26) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__28 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
              else
                (do
                  let w__30 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__AMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__30 : Bool)
                  then
                    (do
                      let w__34 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__32 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__32) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__34 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__38 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__38 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__45 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       let w__40 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                       (pure (((! w__40) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__42) +++ (_get_HCR_EL2_Type_TGE
                                          w__43)) != 0b11#2) : Bool))))
                              else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__45 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__49 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__49 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
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
                                      else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__53 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
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
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__69 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   if ((← do
                                                        if ((← do
                                                             if ((← do
                                                                  (EL2Enabled ())) : Bool)
                                                             then
                                                               (do
                                                                 let w__59 ← (( do
                                                                   (ELUsingAArch32 EL1) ) : SailM
                                                                   Bool )
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
                                                   else (pure false)) : Bool)
                                              then
                                                (do
                                                  (pure ((← do
                                                        let w__66 ← (( do (HaveEL EL3) ) : SailM
                                                          Bool )
                                                        (pure (((! w__66) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                                              else (pure false)) && ((__HAFGRTR_EL2_AMEVTYPER113_EL0 == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__69 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          let w__73 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (HaveEL EL3)) : Bool)
                                                  then
                                                    (do
                                                      let w__71 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__71) : Bool))))
                                                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__73 : Bool)
                                          then
                                            (do
                                              let w__76 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__75 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__75) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__76 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_AArch32SystemAccessTrap EL3
                                                    (BitVec.toNat 0x03#8))))
                                          else
                                            (do
                                              let w__77 ← (( do (AMEVTYPER1_read 13) ) : SailM
                                                (BitVec 32) )
                                              (R_set t (__get_AMEVTYPER1 w__77))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__87 ← (( do
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
                                    let w__81 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__81) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__85 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__85) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__87 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__91 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__89 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__89) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__91 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__95 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__95 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__99 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__97 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__97) : Bool))))
                                  else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__99 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__103 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__103 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__107 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__105 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__105) : Bool))))
                                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__107 : Bool)
                                  then
                                    (do
                                      let w__110 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__109 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__109) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__110 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      let w__111 ← (( do (AMEVTYPER1_read 13) ) : SailM
                                        (BitVec 32) )
                                      (R_set t (__get_AMEVTYPER1 w__111)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__121 ← (( do
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
                                        let w__115 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__115) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__119 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__119) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__121 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__125 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__123 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__123) : Bool))))
                              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__125 : Bool)
                      then
                        (do
                          let w__128 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__127 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__127) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__128 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          let w__129 ← (( do (AMEVTYPER1_read 13) ) : SailM (BitVec 32) )
                          (R_set t (__get_AMEVTYPER1 w__129)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__130 ← (( do (AMEVTYPER1_read 13) ) : SailM (BitVec 32) )
                      (R_set t (__get_AMEVTYPER1 w__130)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegRead32_bc839289c9bacd64 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__10 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__10)
  let w__11 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HAFGRTR_EL2_AMEVTYPER14_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVTYPER14_EL0 w__11)
  let w__12 ← (( do (IsG1ActivityMonitorImplemented 4) ) : SailM Bool )
  if ((! w__12) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__22 ← (( do
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
                                let w__16 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__16) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__20 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__20) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__22 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__24 ← (( do
                (pure ((← do
                      let w__23 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                      (pure (((! w__23) : Bool)))) && ((__AMUSERENR_EL0_EN == 0#1) : Bool))) ) :
                SailM Bool )
              if (w__24 : Bool)
              then
                (do
                  let w__28 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__26 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__26) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__28 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
              else
                (do
                  let w__30 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__AMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__30 : Bool)
                  then
                    (do
                      let w__34 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__32 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__32) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__34 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__38 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__38 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__45 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       let w__40 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                       (pure (((! w__40) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__42) +++ (_get_HCR_EL2_Type_TGE
                                          w__43)) != 0b11#2) : Bool))))
                              else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__45 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__49 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__49 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
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
                                      else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__53 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
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
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__69 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   if ((← do
                                                        if ((← do
                                                             if ((← do
                                                                  (EL2Enabled ())) : Bool)
                                                             then
                                                               (do
                                                                 let w__59 ← (( do
                                                                   (ELUsingAArch32 EL1) ) : SailM
                                                                   Bool )
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
                                                   else (pure false)) : Bool)
                                              then
                                                (do
                                                  (pure ((← do
                                                        let w__66 ← (( do (HaveEL EL3) ) : SailM
                                                          Bool )
                                                        (pure (((! w__66) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                                              else (pure false)) && ((__HAFGRTR_EL2_AMEVTYPER14_EL0 == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__69 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          let w__73 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (HaveEL EL3)) : Bool)
                                                  then
                                                    (do
                                                      let w__71 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__71) : Bool))))
                                                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__73 : Bool)
                                          then
                                            (do
                                              let w__76 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__75 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__75) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__76 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_AArch32SystemAccessTrap EL3
                                                    (BitVec.toNat 0x03#8))))
                                          else
                                            (do
                                              let w__77 ← (( do (AMEVTYPER1_read 4) ) : SailM
                                                (BitVec 32) )
                                              (R_set t (__get_AMEVTYPER1 w__77))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__87 ← (( do
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
                                    let w__81 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__81) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__85 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__85) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__87 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__91 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__89 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__89) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__91 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__95 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__95 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__99 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__97 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__97) : Bool))))
                                  else (pure false)) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__99 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__103 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCPTR_TAM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__103 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__107 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__105 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__105) : Bool))))
                                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__107 : Bool)
                                  then
                                    (do
                                      let w__110 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__109 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__109) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__110 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      let w__111 ← (( do (AMEVTYPER1_read 4) ) : SailM (BitVec 32)
                                        )
                                      (R_set t (__get_AMEVTYPER1 w__111)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__121 ← (( do
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
                                        let w__115 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__115) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__119 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__119) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__121 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__125 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__123 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__123) : Bool))))
                              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__125 : Bool)
                      then
                        (do
                          let w__128 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__127 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__127) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__128 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          let w__129 ← (( do (AMEVTYPER1_read 4) ) : SailM (BitVec 32) )
                          (R_set t (__get_AMEVTYPER1 w__129)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__130 ← (( do (AMEVTYPER1_read 4) ) : SailM (BitVec 32) )
                      (R_set t (__get_AMEVTYPER1 w__130)))
                  else (pure (()))))))


end ArmFull.Functions
