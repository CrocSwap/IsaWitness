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
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0057
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0062
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0083
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0199
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0212
public import ArmFull.Fn.M0219
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
                          let w__24 ← (( do
                            if ((← do
                                 (HaveEL EL3)) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL3))
                            else (pure false) ) : SailM Bool )
                          if (w__24 : Bool)
                          then
                            (do
                              let w__25 ← (( do (EAEisOne ()) ) : SailM Bool )
                              if (w__25 : Bool)
                              then
                                (do
                                  let w__26 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (MAIR1_NS_write (Mk_MAIR1_Type w__26)))
                              else
                                (do
                                  let w__27 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (NMRR_NS_write (Mk_NMRR_Type w__27))))
                          else
                            (do
                              let w__28 ← (( do (EAEisOne ()) ) : SailM Bool )
                              if (w__28 : Bool)
                              then
                                (do
                                  let w__29 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (MAIR1_write (Mk_MAIR1_Type w__29)))
                              else
                                (do
                                  let w__30 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (NMRR_write (Mk_NMRR_Type w__30)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__33 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__33 : Bool)
              then
                (do
                  let w__34 ← (( do (EAEisOne ()) ) : SailM Bool )
                  if (w__34 : Bool)
                  then
                    (do
                      let w__35 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (MAIR1_NS_write (Mk_MAIR1_Type w__35)))
                  else
                    (do
                      let w__36 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (NMRR_NS_write (Mk_NMRR_Type w__36))))
              else
                (do
                  let w__37 ← (( do (EAEisOne ()) ) : SailM Bool )
                  if (w__37 : Bool)
                  then
                    (do
                      let w__38 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (MAIR1_write (Mk_MAIR1_Type w__38)))
                  else
                    (do
                      let w__39 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (NMRR_write (Mk_NMRR_Type w__39)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__41 ← (( do
                    if (((__SCR_NS == 0#1) : Bool) : Bool)
                    then
                      (do
                        let w__40 ← (( do readReg CP15SDISABLE ) : SailM Signal )
                        (pure (((BEq.beq w__40 Signal_High) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__41 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__43 ← (( do
                        if (((__SCR_NS == 0#1) : Bool) : Bool)
                        then
                          (do
                            let w__42 ← (( do readReg CP15SDISABLE2 ) : SailM Signal )
                            (pure (((BEq.beq w__42 Signal_High) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__43 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__44 ← (( do (EAEisOne ()) ) : SailM Bool )
                          if (w__44 : Bool)
                          then
                            (do
                              if ((__SCR_NS == 0#1) : Bool)
                              then
                                (do
                                  let w__45 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (MAIR1_S_write (Mk_MAIR1_Type w__45)))
                              else
                                (do
                                  let w__46 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (MAIR1_NS_write (Mk_MAIR1_Type w__46))))
                          else
                            (do
                              if ((__SCR_NS == 0#1) : Bool)
                              then
                                (do
                                  let w__47 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  writeReg NMRR_S (Mk_NMRR_Type w__47))
                              else
                                (do
                                  let w__48 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (NMRR_NS_write (Mk_NMRR_Type w__48)))))))
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
                  let w__14 ← (( do
                    if ((← do
                         (HaveEL EL3)) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL3))
                    else (pure false) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__15 ← (( do readReg PAR_NS ) : SailM (BitVec 64) )
                      let w__16 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg PAR_NS (Sail.BitVec.updateSubrange w__15 31 0 w__16))
                  else
                    (do
                      let w__17 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
                      let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange w__17 31 0 w__18)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__21 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__21 : Bool)
              then
                (do
                  let w__22 ← (( do readReg PAR_NS ) : SailM (BitVec 64) )
                  let w__23 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  writeReg PAR_NS (Sail.BitVec.updateSubrange w__22 31 0 w__23))
              else
                (do
                  let w__24 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
                  let w__25 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange w__24 31 0 w__25)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__26 ← (( do readReg PAR_S ) : SailM (BitVec 64) )
                      let w__27 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg PAR_S (Sail.BitVec.updateSubrange w__26 31 0 w__27))
                  else
                    (do
                      let w__28 ← (( do readReg PAR_NS ) : SailM (BitVec 64) )
                      let w__29 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg PAR_NS (Sail.BitVec.updateSubrange w__28 31 0 w__29)))
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
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__19 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__28 ← (( do
            if ((← do
                 let w__20 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                 (pure (((! w__20) : Bool)))) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                     then
                       (do
                         let w__22 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__23 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__22) +++ (_get_PMUSERENR_EL0_Type_EN
                                 w__23)) == 0b00#2) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__25 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                          (pure (((! w__25) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
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
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
          else
            (do
              let w__34 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__PMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
              if (w__34 : Bool)
              then
                (do
                  let w__38 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__36 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__36) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__38 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__42 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__42 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__54 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__44 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool
                                               )
                                             (pure (((! w__44) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__46 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        let w__47 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_HCR_EL2_Type_E2H w__46) +++ (_get_HCR_EL2_Type_TGE
                                                w__47)) != 0b11#2) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__51 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__51) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGWTR_EL2_PMCCFILTR_EL0 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__54 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__58 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__56 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__56) : Bool))))
                              else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__58 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__62 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__62 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__66 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__64 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__64) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__66 : Bool)
                              then
                                (do
                                  let w__69 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__68 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__68) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__69 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  let w__70 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (PMCCFILTR_write (Mk_PMCCFILTR_Type w__70))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__80 ← (( do
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
                                let w__74 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__74) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__78 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__78) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__80 : Bool)
          then sailThrow ((Error_Undefined ()))
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
                      else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
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
                          else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
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
                          let w__96 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (PMCCFILTR_write (Mk_PMCCFILTR_Type w__96)))))))
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
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
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
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
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
                      let w__114 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (PMCCFILTR_write (Mk_PMCCFILTR_Type w__114)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__115 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (PMCCFILTR_write (Mk_PMCCFILTR_Type w__115)))
              else (pure (())))))


end ArmFull.Functions
