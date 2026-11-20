module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0069
public import ArmFull.Fn.M0070
public import ArmFull.Fn.M0072
public import ArmFull.Fn.M0074
public import ArmFull.Fn.M0076
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0199
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
def ICC_IGRPEN1_EL3_SysRegWrite_b957139b0969fa79 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ICC_IGRPEN1_EL3 (Mk_ICC_IGRPEN1_EL3_Type w__2)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_PMR_EL1_SysRegWrite_4d3a3fb3d6e1e44e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__2)
  let w__3 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TC : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TC w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_IMO : (BitVec 1) := (_get_HCR_EL2_Type_IMO w__5)
  let w__6 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__6)
  let w__7 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__16 ← (( do
            if ((← do
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
                 else (pure false)) : Bool)
            then
              (do
                let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let w__15 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure (((((_get_SCR_EL3_Type_IRQ w__14) +++ (_get_SCR_EL3_Type_FIQ w__15)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__16 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__ICH_HCR_EL2_TC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_FMO == 1#1) : Bool))) ) : SailM Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          let w__21 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICV_PMR_EL1 (Mk_ICV_PMR_EL1_Type w__21))
                      else
                        (do
                          let w__23 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__HCR_EL2_IMO == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__23 : Bool)
                          then
                            (do
                              let w__24 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ICV_PMR_EL1 (Mk_ICV_PMR_EL1_Type w__24))
                          else
                            (do
                              let w__28 ← (( do
                                if ((← do
                                     (HaveEL EL3)) : Bool)
                                then
                                  (do
                                    let w__26 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    let w__27 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    (pure (((((_get_SCR_EL3_Type_IRQ w__26) +++ (_get_SCR_EL3_Type_FIQ
                                            w__27)) == 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__28 : Bool)
                              then
                                (do
                                  let w__30 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__30 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__31 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ICC_PMR_EL1 (Mk_ICC_PMR_EL1_Type w__31))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__40 ← (( do
                if ((← do
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
                     else (pure false)) : Bool)
                then
                  (do
                    let w__38 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__39 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__38) +++ (_get_SCR_EL3_Type_FIQ w__39)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__40 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__44 ← (( do
                        if ((← do
                             (HaveEL EL3)) : Bool)
                        then
                          (do
                            let w__42 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            let w__43 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure (((((_get_SCR_EL3_Type_IRQ w__42) +++ (_get_SCR_EL3_Type_FIQ w__43)) == 0b11#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          let w__46 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__46 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__47 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICC_PMR_EL1 (Mk_ICC_PMR_EL1_Type w__47)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__48 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ICC_PMR_EL1 (Mk_ICC_PMR_EL1_Type w__48)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_SGI0R_EL1_SysRegWrite_97ea36eebda9c84c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__2)
  let w__3 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TC : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TC w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_IMO : (BitVec 1) := (_get_HCR_EL2_Type_IMO w__5)
  let w__6 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__6)
  let w__7 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__16 ← (( do
            if ((← do
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
                 else (pure false)) : Bool)
            then
              (do
                let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let w__15 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure (((((_get_SCR_EL3_Type_IRQ w__14) +++ (_get_SCR_EL3_Type_FIQ w__15)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__16 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__ICH_HCR_EL2_TC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_FMO == 1#1) : Bool))) ) : SailM Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__22 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__HCR_EL2_IMO == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__22 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__26 ← (( do
                                if ((← do
                                     (HaveEL EL3)) : Bool)
                                then
                                  (do
                                    let w__24 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    let w__25 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    (pure (((((_get_SCR_EL3_Type_IRQ w__24) +++ (_get_SCR_EL3_Type_FIQ
                                            w__25)) == 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__26 : Bool)
                              then
                                (do
                                  let w__28 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__28 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__29 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ICC_SGI0R_EL1 (Mk_ICC_SGI0R_EL1_Type w__29))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__38 ← (( do
                if ((← do
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
                     else (pure false)) : Bool)
                then
                  (do
                    let w__36 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__37 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__36) +++ (_get_SCR_EL3_Type_FIQ w__37)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__38 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__42 ← (( do
                        if ((← do
                             (HaveEL EL3)) : Bool)
                        then
                          (do
                            let w__40 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            let w__41 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure (((((_get_SCR_EL3_Type_IRQ w__40) +++ (_get_SCR_EL3_Type_FIQ w__41)) == 0b11#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__42 : Bool)
                      then
                        (do
                          let w__44 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__44 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICC_SGI0R_EL1 (Mk_ICC_SGI0R_EL1_Type w__45)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__46 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ICC_SGI0R_EL1 (Mk_ICC_SGI0R_EL1_Type w__46)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_SGI1R_EL1_SysRegWrite_bd688469b6075cd1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__2)
  let w__3 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TC : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TC w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_IMO : (BitVec 1) := (_get_HCR_EL2_Type_IMO w__5)
  let w__6 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__6)
  let w__7 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__16 ← (( do
            if ((← do
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
                 else (pure false)) : Bool)
            then
              (do
                let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let w__15 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure (((((_get_SCR_EL3_Type_IRQ w__14) +++ (_get_SCR_EL3_Type_FIQ w__15)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__16 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__ICH_HCR_EL2_TC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_FMO == 1#1) : Bool))) ) : SailM Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__22 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__HCR_EL2_IMO == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__22 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                          else
                            (do
                              let w__26 ← (( do
                                if ((← do
                                     (HaveEL EL3)) : Bool)
                                then
                                  (do
                                    let w__24 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    let w__25 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    (pure (((((_get_SCR_EL3_Type_IRQ w__24) +++ (_get_SCR_EL3_Type_FIQ
                                            w__25)) == 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__26 : Bool)
                              then
                                (do
                                  let w__28 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__28 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__29 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ICC_SGI1R_EL1 (Mk_ICC_SGI1R_EL1_Type w__29))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__38 ← (( do
                if ((← do
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
                     else (pure false)) : Bool)
                then
                  (do
                    let w__36 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__37 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__36) +++ (_get_SCR_EL3_Type_FIQ w__37)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__38 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__42 ← (( do
                        if ((← do
                             (HaveEL EL3)) : Bool)
                        then
                          (do
                            let w__40 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            let w__41 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure (((((_get_SCR_EL3_Type_IRQ w__40) +++ (_get_SCR_EL3_Type_FIQ w__41)) == 0b11#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__42 : Bool)
                      then
                        (do
                          let w__44 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__44 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICC_SGI1R_EL1 (Mk_ICC_SGI1R_EL1_Type w__45)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_SRE_EL3_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__46 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ICC_SGI1R_EL1 (Mk_ICC_SGI1R_EL1_Type w__46)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_SRE_EL1_SysRegWrite_b4fd95205f21b2e7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_Enable : (BitVec 1) := (_get_ICC_SRE_EL3_Type_Enable w__2)
  let w__3 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_Enable : (BitVec 1) := (_get_ICC_SRE_EL2_Type_Enable w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__11 ← (( do
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
                  else (pure false)) && ((__ICC_SRE_EL3_Enable == 0#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__ICC_SRE_EL2_Enable == 0#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__15 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__ICC_SRE_EL3_Enable == 0#1) : Bool))) ) : SailM Bool )
                  if (w__15 : Bool)
                  then
                    (do
                      let w__17 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__17 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__18 ← (( do (HaveEL EL3) ) : SailM Bool )
                      if (w__18 : Bool)
                      then
                        (do
                          if ((__SCR_EL3_NS == 0#1) : Bool)
                          then
                            (do
                              let w__19 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ICC_SRE_EL1_S (Mk_ICC_SRE_EL1_Type w__19))
                          else
                            (do
                              let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ICC_SRE_EL1_NS (Mk_ICC_SRE_EL1_Type w__20)))
                      else
                        (do
                          let w__21 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (ICC_SRE_EL1_write (Mk_ICC_SRE_EL1_Type w__21)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__28 ← (( do
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
                      else (pure false)) && ((__ICC_SRE_EL3_Enable == 0#1) : Bool))) ) : SailM Bool
                )
              if (w__28 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__30 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__ICC_SRE_EL3_Enable == 0#1) : Bool))) ) : SailM Bool )
                  if (w__30 : Bool)
                  then
                    (do
                      let w__32 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__32 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__33 ← (( do (HaveEL EL3) ) : SailM Bool )
                      if (w__33 : Bool)
                      then
                        (do
                          if ((__SCR_EL3_NS == 0#1) : Bool)
                          then
                            (do
                              let w__34 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ICC_SRE_EL1_S (Mk_ICC_SRE_EL1_Type w__34))
                          else
                            (do
                              let w__35 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ICC_SRE_EL1_NS (Mk_ICC_SRE_EL1_Type w__35)))
                      else
                        (do
                          let w__36 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (ICC_SRE_EL1_write (Mk_ICC_SRE_EL1_Type w__36))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then
                    (do
                      let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ICC_SRE_EL1_S (Mk_ICC_SRE_EL1_Type w__37))
                  else
                    (do
                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ICC_SRE_EL1_NS (Mk_ICC_SRE_EL1_Type w__38)))
              else (pure (())))))


end ArmFull.Functions
