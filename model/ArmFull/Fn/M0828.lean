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
import ArmFull.Fn.M0035
import ArmFull.Fn.M0036
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0054
import ArmFull.Fn.M0056
import ArmFull.Fn.M0059
import ArmFull.Fn.M0061
import ArmFull.Fn.M0081
import ArmFull.Fn.M0121
import ArmFull.Fn.M0176
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0196
import ArmFull.Fn.M0200
import ArmFull.Fn.M0201
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0213
import ArmFull.Fn.M0220
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

/-- Type quantifiers: t : Int -/
def PRRR_SysRegWrite32_d60dcdae1cc2429d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T10 : (BitVec 1) := (_get_HSTR_EL2_Type_T10 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T10 : (BitVec 1) := (_get_HSTR_Type_T10 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TVM : (BitVec 1) := (_get_HCR_EL2_Type_TVM w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TVM : (BitVec 1) := (_get_HCR_Type_TVM w__4)
  let w__5 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__7 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__7) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T10 == 1#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T10 == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__17 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__15) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TVM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TVM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__23 ← (( do
                            if (((HaveEL EL3) : Bool) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL3))
                            else (pure false) ) : SailM Bool )
                          if (w__23 : Bool)
                          then
                            (do
                              let w__24 ← (( do (EAEisOne ()) ) : SailM Bool )
                              if (w__24 : Bool)
                              then
                                (do
                                  let w__25 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (MAIR0_NS_write (Mk_MAIR0_Type w__25)))
                              else
                                (do
                                  let w__26 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (PRRR_NS_write (Mk_PRRR_Type w__26))))
                          else
                            (do
                              let w__27 ← (( do (EAEisOne ()) ) : SailM Bool )
                              if (w__27 : Bool)
                              then
                                (do
                                  let w__28 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (MAIR0_write (Mk_MAIR0_Type w__28)))
                              else
                                (do
                                  let w__29 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (PRRR_write (Mk_PRRR_Type w__29)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__31 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__31 : Bool)
              then
                (do
                  let w__32 ← (( do (EAEisOne ()) ) : SailM Bool )
                  if (w__32 : Bool)
                  then
                    (do
                      let w__33 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (MAIR0_NS_write (Mk_MAIR0_Type w__33)))
                  else
                    (do
                      let w__34 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (PRRR_NS_write (Mk_PRRR_Type w__34))))
              else
                (do
                  let w__35 ← (( do (EAEisOne ()) ) : SailM Bool )
                  if (w__35 : Bool)
                  then
                    (do
                      let w__36 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (MAIR0_write (Mk_MAIR0_Type w__36)))
                  else
                    (do
                      let w__37 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (PRRR_write (Mk_PRRR_Type w__37)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__39 ← (( do
                    if (((__SCR_NS == 0#1) : Bool) : Bool)
                    then
                      (do
                        let w__38 ← (( do readReg CP15SDISABLE ) : SailM Signal )
                        (pure (((BEq.beq w__38 Signal_High) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__39 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__41 ← (( do
                        if (((__SCR_NS == 0#1) : Bool) : Bool)
                        then
                          (do
                            let w__40 ← (( do readReg CP15SDISABLE2 ) : SailM Signal )
                            (pure (((BEq.beq w__40 Signal_High) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__41 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__42 ← (( do (EAEisOne ()) ) : SailM Bool )
                          if (w__42 : Bool)
                          then
                            (do
                              if ((__SCR_NS == 0#1) : Bool)
                              then
                                (do
                                  let w__43 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (MAIR0_S_write (Mk_MAIR0_Type w__43)))
                              else
                                (do
                                  let w__44 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (MAIR0_NS_write (Mk_MAIR0_Type w__44))))
                          else
                            (do
                              if ((__SCR_NS == 0#1) : Bool)
                              then
                                (do
                                  let w__45 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  writeReg PRRR_S (Mk_PRRR_Type w__45))
                              else
                                (do
                                  let w__46 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (PRRR_NS_write (Mk_PRRR_Type w__46)))))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SCR_SysRegWrite32_4891195fead51a46 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T1 : (BitVec 1) := (_get_HSTR_EL2_Type_T1 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T1 : (BitVec 1) := (_get_HSTR_Type_T1 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__5) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T1 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T1 == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__15 ← (( do
                    if ((← do
                         let w__12 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                         (pure (((! w__12) : Bool)))) : Bool)
                    then
                      (do
                        let w__13 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        (pure (((((_get_SCR_EL3_Type_NS w__13) +++ (_get_SCR_EL3_Type_EEL2 w__14)) == 0b01#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__15 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__17 ← (( do
                        (pure ((← do
                              let w__16 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__16) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__17 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else sailThrow ((Error_Undefined ()))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  writeReg SCR (Mk_SCR_Type w__18))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SCTLR_SysRegWrite32_88c9496795c226a4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T1 : (BitVec 1) := (_get_HSTR_EL2_Type_T1 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T1 : (BitVec 1) := (_get_HSTR_Type_T1 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TVM : (BitVec 1) := (_get_HCR_EL2_Type_TVM w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TVM : (BitVec 1) := (_get_HCR_Type_TVM w__4)
  let w__5 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__7 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__7) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T1 == 1#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T1 == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__17 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__15) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TVM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TVM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__23 ← (( do
                            if (((HaveEL EL3) : Bool) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL3))
                            else (pure false) ) : SailM Bool )
                          if (w__23 : Bool)
                          then
                            (do
                              let w__24 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (__set_SCTLR_NS (Mk_SCTLR_Type w__24)))
                          else
                            (do
                              let w__25 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (__set_SCTLR (Mk_SCTLR_Type w__25))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__27 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__27 : Bool)
              then
                (do
                  let w__28 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (__set_SCTLR_NS (Mk_SCTLR_Type w__28)))
              else
                (do
                  let w__29 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (__set_SCTLR (Mk_SCTLR_Type w__29))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__31 ← (( do
                    if (((__SCR_NS == 0#1) : Bool) : Bool)
                    then
                      (do
                        let w__30 ← (( do readReg CP15SDISABLE ) : SailM Signal )
                        (pure (((BEq.beq w__30 Signal_High) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__31 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__33 ← (( do
                        if (((__SCR_NS == 0#1) : Bool) : Bool)
                        then
                          (do
                            let w__32 ← (( do readReg CP15SDISABLE2 ) : SailM Signal )
                            (pure (((BEq.beq w__32 Signal_High) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__33 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          if ((__SCR_NS == 0#1) : Bool)
                          then
                            (do
                              let w__34 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (__set_SCTLR_S (Mk_SCTLR_Type w__34)))
                          else
                            (do
                              let w__35 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (__set_SCTLR_NS (Mk_SCTLR_Type w__35))))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SDCR_SysRegWrite32_4a9ed44cdafd01dd (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T1 : (BitVec 1) := (_get_HSTR_EL2_Type_T1 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T1 : (BitVec 1) := (_get_HSTR_Type_T1 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__5) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T1 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T1 == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__15 ← (( do
                    if ((← do
                         let w__12 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                         (pure (((! w__12) : Bool)))) : Bool)
                    then
                      (do
                        let w__13 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        (pure (((((_get_SCR_EL3_Type_NS w__13) +++ (_get_SCR_EL3_Type_EEL2 w__14)) == 0b01#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__15 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__17 ← (( do
                        (pure ((← do
                              let w__16 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__16) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__17 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                      else sailThrow ((Error_Undefined ()))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__18 ← (( do readReg CP15SDISABLE2 ) : SailM Signal )
                  if ((BEq.beq w__18 Signal_High) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg SDCR (Mk_SDCR_Type w__19)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SDER_SysRegWrite32_78d36c9dd1d8d07c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T1 : (BitVec 1) := (_get_HSTR_EL2_Type_T1 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T1 : (BitVec 1) := (_get_HSTR_Type_T1 w__2)
  let w__3 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__5) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T1 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T1 == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__12 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
                  if ((! w__12) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__18 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__14) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__16 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__17 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__16) +++ (_get_MDCR_EL2_Type_TDA
                                    w__17)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__18 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__21 ← (( do
                            (pure ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
                                  then
                                    (do
                                      let w__19 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__19) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__21 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__22 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (SDER_write (Mk_SDER_Type w__22))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do readReg CP15SDISABLE2 ) : SailM Signal )
                  if ((BEq.beq w__23 Signal_High) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__24 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (SDER_write (Mk_SDER_Type w__24))))
              else (pure (())))))


end ArmFull.Functions
