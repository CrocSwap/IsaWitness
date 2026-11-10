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
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0054
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0059
import ArmFull.Fn.M0062
import ArmFull.Fn.M0064
import ArmFull.Fn.M0073
import ArmFull.Fn.M0082
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0200
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
def MVBAR_SysRegWrite32_b51bf66bf3dc6e40 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__2)
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
                  else (pure false)) && ((__HSTR_EL2_T12 == 1#1) : Bool))) ) : SailM Bool )
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
                      else (pure false)) && ((__HSTR_T12 == 1#1) : Bool))) ) : SailM Bool )
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
                  let w__18 ← (( do readReg CP15SDISABLE ) : SailM Signal )
                  if ((BEq.beq w__18 Signal_High) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__19 ← (( do readReg CP15SDISABLE2 ) : SailM Signal )
                      if ((BEq.beq w__19 Signal_High) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__20 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          writeReg MVBAR (Mk_MVBAR_Type w__20))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def NMRR_SysRegWrite32_d7c63fb9ed572aa1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                  (MAIR1_NS_write (Mk_MAIR1_Type w__25)))
                              else
                                (do
                                  let w__26 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (NMRR_NS_write (Mk_NMRR_Type w__26))))
                          else
                            (do
                              let w__27 ← (( do (EAEisOne ()) ) : SailM Bool )
                              if (w__27 : Bool)
                              then
                                (do
                                  let w__28 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (MAIR1_write (Mk_MAIR1_Type w__28)))
                              else
                                (do
                                  let w__29 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (NMRR_write (Mk_NMRR_Type w__29)))))))))
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
                      (MAIR1_NS_write (Mk_MAIR1_Type w__33)))
                  else
                    (do
                      let w__34 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (NMRR_NS_write (Mk_NMRR_Type w__34))))
              else
                (do
                  let w__35 ← (( do (EAEisOne ()) ) : SailM Bool )
                  if (w__35 : Bool)
                  then
                    (do
                      let w__36 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (MAIR1_write (Mk_MAIR1_Type w__36)))
                  else
                    (do
                      let w__37 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (NMRR_write (Mk_NMRR_Type w__37)))))
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
                                  (MAIR1_S_write (Mk_MAIR1_Type w__43)))
                              else
                                (do
                                  let w__44 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (MAIR1_NS_write (Mk_MAIR1_Type w__44))))
                          else
                            (do
                              if ((__SCR_NS == 0#1) : Bool)
                              then
                                (do
                                  let w__45 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  writeReg NMRR_S (Mk_NMRR_Type w__45))
                              else
                                (do
                                  let w__46 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (NMRR_NS_write (Mk_NMRR_Type w__46)))))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def NSACR_SysRegWrite32_78181d9f16e34b35 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      writeReg NSACR (Mk_NSACR_Type w__19)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PAR_SysRegWrite32_b3494b8d6e542bfa (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__2)
  let w__3 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__3)
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
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
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
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__13 ← (( do
                    if (((HaveEL EL3) : Bool) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL3))
                    else (pure false) ) : SailM Bool )
                  if (w__13 : Bool)
                  then
                    (do
                      let w__14 ← (( do readReg PAR_NS ) : SailM (BitVec 64) )
                      let w__15 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg PAR_NS (Sail.BitVec.updateSubrange w__14 31 0 w__15))
                  else
                    (do
                      let w__16 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
                      let w__17 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange w__16 31 0 w__17)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__19 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__19 : Bool)
              then
                (do
                  let w__20 ← (( do readReg PAR_NS ) : SailM (BitVec 64) )
                  let w__21 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  writeReg PAR_NS (Sail.BitVec.updateSubrange w__20 31 0 w__21))
              else
                (do
                  let w__22 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
                  let w__23 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange w__22 31 0 w__23)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__24 ← (( do readReg PAR_S ) : SailM (BitVec 64) )
                      let w__25 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg PAR_S (Sail.BitVec.updateSubrange w__24 31 0 w__25))
                  else
                    (do
                      let w__26 ← (( do readReg PAR_NS ) : SailM (BitVec 64) )
                      let w__27 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg PAR_NS (Sail.BitVec.updateSubrange w__26 31 0 w__27)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PMCCFILTR_SysRegWrite32_380c0e93b25f3214 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TPM : (BitVec 1) := (_get_MDCR_EL3_Type_TPM w__1)
  let w__2 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __PMUSERENR_EL0_EN : (BitVec 1) := (_get_PMUSERENR_EL0_Type_EN w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
  let __PMUSERENR_EN : (BitVec 1) := (_get_PMUSERENR_Type_EN w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__5)
  let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__6)
  let w__7 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMCCFILTR_EL0 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMCCFILTR_EL0 w__7)
  let w__8 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__8)
  let w__9 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPM : (BitVec 1) := (_get_HDCR_Type_TPM w__9)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__18 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        if ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                        then
                          (do
                            let w__12 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__12) == 1#1) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                   else (pure false)) : Bool)
              then
                (do
                  let w__16 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                  (pure (((! w__16) : Bool))))
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__18 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__27 ← (( do
            if ((← do
                 let w__19 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                 (pure (((! w__19) : Bool)))) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                     then
                       (do
                         let w__21 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__22 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__21) +++ (_get_PMUSERENR_EL0_Type_EN
                                 w__22)) == 0b00#2) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__24 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                          (pure (((! w__24) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
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
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
          else
            (do
              let w__33 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__PMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
              if (w__33 : Bool)
              then
                (do
                  let w__37 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__35 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__35) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__37 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__41 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__41 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__51 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     if ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              let w__43 ← (( do (ELUsingAArch32 EL1) ) : SailM
                                                Bool )
                                              (pure (((! w__43) : Bool))))
                                          else (pure false)) : Bool)
                                     then
                                       (do
                                         let w__45 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                         let w__46 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                         (pure (((((_get_HCR_EL2_Type_E2H w__45) +++ (_get_HCR_EL2_Type_TGE
                                                 w__46)) != 0b11#2) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGWTR_EL2_PMCCFILTR_EL0 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__51 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__55 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__53 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__53) : Bool))))
                              else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__55 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__59 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__59 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__62 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          let w__60 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__60) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__62 : Bool)
                              then
                                (do
                                  let w__65 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__64 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__64) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__65 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  let w__66 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (PMCCFILTR_write (Mk_PMCCFILTR_Type w__66))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__75 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__69 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__69) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__73 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__73) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__75 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__79 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__77 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__77) : Bool))))
                      else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__79 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__83 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__83 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__86 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__84 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__84) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__86 : Bool)
                      then
                        (do
                          let w__89 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__88 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__88) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__89 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          let w__90 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (PMCCFILTR_write (Mk_PMCCFILTR_Type w__90)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__99 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__93 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__93) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__97 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__97) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__99 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__102 ← (( do
                    (pure ((← do
                          if (((HaveEL EL3) : Bool) : Bool)
                          then
                            (do
                              let w__100 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__100) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__102 : Bool)
                  then
                    (do
                      let w__105 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__104 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__104) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__105 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                  else
                    (do
                      let w__106 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (PMCCFILTR_write (Mk_PMCCFILTR_Type w__106)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__107 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (PMCCFILTR_write (Mk_PMCCFILTR_Type w__107)))
              else (pure (())))))


end ArmFull.Functions
