module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0196
public import ArmFull.Fn.M0199
public import ArmFull.Fn.M0201
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
def TTBCR2_SysRegWrite32_06c6fc8db37664f3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T2 : (BitVec 1) := (_get_HSTR_EL2_Type_T2 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T2 : (BitVec 1) := (_get_HSTR_Type_T2 w__2)
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
                  else (pure false)) && ((__HSTR_EL2_T2 == 1#1) : Bool))) ) : SailM Bool )
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
                      else (pure false)) && ((__HSTR_T2 == 1#1) : Bool))) ) : SailM Bool )
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
                              let w__25 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (TTBCR2_NS_write (Mk_TTBCR2_Type w__25)))
                          else
                            (do
                              let w__26 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (TTBCR2_write (Mk_TTBCR2_Type w__26))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__29 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__29 : Bool)
              then
                (do
                  let w__30 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TTBCR2_NS_write (Mk_TTBCR2_Type w__30)))
              else
                (do
                  let w__31 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TTBCR2_write (Mk_TTBCR2_Type w__31))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__33 ← (( do
                    if (((__SCR_NS == 0#1) : Bool) : Bool)
                    then
                      (do
                        let w__32 ← (( do readReg CP15SDISABLE ) : SailM Signal )
                        (pure (((BEq.beq w__32 Signal_High) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__33 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__35 ← (( do
                        if (((__SCR_NS == 0#1) : Bool) : Bool)
                        then
                          (do
                            let w__34 ← (( do readReg CP15SDISABLE2 ) : SailM Signal )
                            (pure (((BEq.beq w__34 Signal_High) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__35 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          if ((__SCR_NS == 0#1) : Bool)
                          then
                            (do
                              let w__36 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              writeReg TTBCR2_S (Mk_TTBCR2_Type w__36))
                          else
                            (do
                              let w__37 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (TTBCR2_NS_write (Mk_TTBCR2_Type w__37))))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TTBCR_SysRegWrite32_4607ff14cabf6694 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T2 : (BitVec 1) := (_get_HSTR_EL2_Type_T2 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T2 : (BitVec 1) := (_get_HSTR_Type_T2 w__2)
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
                  else (pure false)) && ((__HSTR_EL2_T2 == 1#1) : Bool))) ) : SailM Bool )
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
                      else (pure false)) && ((__HSTR_T2 == 1#1) : Bool))) ) : SailM Bool )
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
                              let w__25 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (TTBCR_NS_write (Mk_TTBCR_Type w__25)))
                          else
                            (do
                              let w__26 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (TTBCR_write (Mk_TTBCR_Type w__26))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__29 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__29 : Bool)
              then
                (do
                  let w__30 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TTBCR_NS_write (Mk_TTBCR_Type w__30)))
              else
                (do
                  let w__31 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TTBCR_write (Mk_TTBCR_Type w__31))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__33 ← (( do
                    if (((__SCR_NS == 0#1) : Bool) : Bool)
                    then
                      (do
                        let w__32 ← (( do readReg CP15SDISABLE ) : SailM Signal )
                        (pure (((BEq.beq w__32 Signal_High) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__33 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__35 ← (( do
                        if (((__SCR_NS == 0#1) : Bool) : Bool)
                        then
                          (do
                            let w__34 ← (( do readReg CP15SDISABLE2 ) : SailM Signal )
                            (pure (((BEq.beq w__34 Signal_High) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__35 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          if ((__SCR_NS == 0#1) : Bool)
                          then
                            (do
                              let w__36 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              writeReg TTBCR_S (Mk_TTBCR_Type w__36))
                          else
                            (do
                              let w__37 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (TTBCR_NS_write (Mk_TTBCR_Type w__37))))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TTBR0_SysRegWrite32_455c3a8e0a51a871 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T2 : (BitVec 1) := (_get_HSTR_EL2_Type_T2 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T2 : (BitVec 1) := (_get_HSTR_Type_T2 w__2)
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
                  else (pure false)) && ((__HSTR_EL2_T2 == 1#1) : Bool))) ) : SailM Bool )
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
                      else (pure false)) && ((__HSTR_T2 == 1#1) : Bool))) ) : SailM Bool )
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
                              let w__25 ← (( do readReg TTBR0_NS ) : SailM (BitVec 64) )
                              let w__26 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              writeReg TTBR0_NS (Sail.BitVec.updateSubrange w__25 31 0 w__26))
                          else
                            (do
                              let w__27 ← (( do (TTBR0_read ()) ) : SailM (BitVec 64) )
                              let w__28 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (TTBR0_write
                                (Mk_TTBR0_Type (Sail.BitVec.updateSubrange w__27 31 0 w__28)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__31 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__31 : Bool)
              then
                (do
                  let w__32 ← (( do readReg TTBR0_NS ) : SailM (BitVec 64) )
                  let w__33 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  writeReg TTBR0_NS (Sail.BitVec.updateSubrange w__32 31 0 w__33))
              else
                (do
                  let w__34 ← (( do (TTBR0_read ()) ) : SailM (BitVec 64) )
                  let w__35 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TTBR0_write (Mk_TTBR0_Type (Sail.BitVec.updateSubrange w__34 31 0 w__35)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__37 ← (( do
                    if (((__SCR_NS == 0#1) : Bool) : Bool)
                    then
                      (do
                        let w__36 ← (( do readReg CP15SDISABLE ) : SailM Signal )
                        (pure (((BEq.beq w__36 Signal_High) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__37 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then
                        (do
                          let w__38 ← (( do readReg TTBR0_S ) : SailM (BitVec 64) )
                          let w__39 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          writeReg TTBR0_S (Sail.BitVec.updateSubrange w__38 31 0 w__39))
                      else
                        (do
                          let w__40 ← (( do readReg TTBR0_NS ) : SailM (BitVec 64) )
                          let w__41 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          writeReg TTBR0_NS (Sail.BitVec.updateSubrange w__40 31 0 w__41))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TTBR1_SysRegWrite32_388bd96b6dea14cc (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T2 : (BitVec 1) := (_get_HSTR_EL2_Type_T2 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T2 : (BitVec 1) := (_get_HSTR_Type_T2 w__2)
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
                  else (pure false)) && ((__HSTR_EL2_T2 == 1#1) : Bool))) ) : SailM Bool )
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
                      else (pure false)) && ((__HSTR_T2 == 1#1) : Bool))) ) : SailM Bool )
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
                              let w__25 ← (( do readReg TTBR1_NS ) : SailM (BitVec 64) )
                              let w__26 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              writeReg TTBR1_NS (Sail.BitVec.updateSubrange w__25 31 0 w__26))
                          else
                            (do
                              let w__27 ← (( do (TTBR1_read ()) ) : SailM (BitVec 64) )
                              let w__28 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (TTBR1_write
                                (Mk_TTBR1_Type (Sail.BitVec.updateSubrange w__27 31 0 w__28)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__31 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__31 : Bool)
              then
                (do
                  let w__32 ← (( do readReg TTBR1_NS ) : SailM (BitVec 64) )
                  let w__33 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  writeReg TTBR1_NS (Sail.BitVec.updateSubrange w__32 31 0 w__33))
              else
                (do
                  let w__34 ← (( do (TTBR1_read ()) ) : SailM (BitVec 64) )
                  let w__35 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TTBR1_write (Mk_TTBR1_Type (Sail.BitVec.updateSubrange w__34 31 0 w__35)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__37 ← (( do
                    if (((__SCR_NS == 0#1) : Bool) : Bool)
                    then
                      (do
                        let w__36 ← (( do readReg CP15SDISABLE2 ) : SailM Signal )
                        (pure (((BEq.beq w__36 Signal_High) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__37 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then
                        (do
                          let w__38 ← (( do readReg TTBR1_S ) : SailM (BitVec 64) )
                          let w__39 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          writeReg TTBR1_S (Sail.BitVec.updateSubrange w__38 31 0 w__39))
                      else
                        (do
                          let w__40 ← (( do readReg TTBR1_NS ) : SailM (BitVec 64) )
                          let w__41 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          writeReg TTBR1_NS (Sail.BitVec.updateSubrange w__40 31 0 w__41))))
              else (pure (())))))


end ArmFull.Functions
