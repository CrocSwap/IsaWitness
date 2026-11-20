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
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0070
public import ArmFull.Fn.M0072
public import ArmFull.Fn.M0075
public import ArmFull.Fn.M0076
public import ArmFull.Fn.M0079
public import ArmFull.Fn.M0092
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
def ICC_CTLR_EL3_SysRegWrite_032d9412ecb7b900 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      writeReg ICC_CTLR_EL3 (Mk_ICC_CTLR_EL3_Type w__2)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_DIR_EL1_SysRegWrite_956e5112d301f88c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__2)
  let w__3 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TDIR : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TDIR w__3)
  let w__4 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TC : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TC w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_IMO : (BitVec 1) := (_get_HCR_EL2_Type_IMO w__6)
  let w__7 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__7)
  let w__8 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__8)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__17 ← (( do
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
                let w__15 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let w__16 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure (((((_get_SCR_EL3_Type_IRQ w__15) +++ (_get_SCR_EL3_Type_FIQ w__16)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__17 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__ICH_HCR_EL2_TDIR == 1#1) : Bool))) ) : SailM Bool
                    )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__ICH_HCR_EL2_TC == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__23 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__HCR_EL2_FMO == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__23 : Bool)
                          then
                            (do
                              let w__24 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ICV_DIR_EL1 (Mk_ICV_DIR_EL1_Type w__24))
                          else
                            (do
                              let w__26 ← (( do
                                (pure ((← do
                                      (EL2Enabled ())) && ((__HCR_EL2_IMO == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__26 : Bool)
                              then
                                (do
                                  let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ICV_DIR_EL1 (Mk_ICV_DIR_EL1_Type w__27))
                              else
                                (do
                                  let w__31 ← (( do
                                    if ((← do
                                         (HaveEL EL3)) : Bool)
                                    then
                                      (do
                                        let w__29 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                        let w__30 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                        (pure (((((_get_SCR_EL3_Type_IRQ w__29) +++ (_get_SCR_EL3_Type_FIQ
                                                w__30)) == 0b11#2) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__31 : Bool)
                                  then
                                    (do
                                      let w__33 ← (( do
                                        (pure ((← do
                                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) :
                                        SailM Bool )
                                      if (w__33 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                                  else
                                    (do
                                      let w__34 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg ICC_DIR_EL1 (Mk_ICC_DIR_EL1_Type w__34)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__43 ← (( do
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
                    let w__41 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__42 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__41) +++ (_get_SCR_EL3_Type_FIQ w__42)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__43 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__47 ← (( do
                        if ((← do
                             (HaveEL EL3)) : Bool)
                        then
                          (do
                            let w__45 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            let w__46 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure (((((_get_SCR_EL3_Type_IRQ w__45) +++ (_get_SCR_EL3_Type_FIQ w__46)) == 0b11#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__47 : Bool)
                      then
                        (do
                          let w__49 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__49 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__50 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICC_DIR_EL1 (Mk_ICC_DIR_EL1_Type w__50)))))
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
                      let w__51 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ICC_DIR_EL1 (Mk_ICC_DIR_EL1_Type w__51)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_IGRPEN0_EL1_SysRegWrite_dcea5bb07e468846 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FIQ : (BitVec 1) := (_get_SCR_EL3_Type_FIQ w__2)
  let w__3 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_ICC_IGRPENn_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_ICC_IGRPENn_EL1 w__5)
  let w__6 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TALL0 : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TALL0 w__6)
  let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__7)
  let w__8 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__8)
  let w__9 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__9)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
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
                  else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
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
                  let w__23 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__20 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__20) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HFGWTR_EL2_ICC_IGRPENn_EL1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__25 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__ICH_HCR_EL2_TALL0 == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__25 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__27 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__HCR_EL2_FMO == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__27 : Bool)
                          then
                            (do
                              let w__28 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ICV_IGRPEN0_EL1 (Mk_ICV_IGRPEN0_EL1_Type w__28))
                          else
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__30 : Bool)
                              then
                                (do
                                  let w__32 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__32 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__33 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ICC_IGRPEN0_EL1 (Mk_ICC_IGRPEN0_EL1_Type w__33))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__40 ← (( do
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
                      else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
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
                      let w__42 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
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
                          writeReg ICC_IGRPEN0_EL1 (Mk_ICC_IGRPEN0_EL1_Type w__45)))))
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
                      writeReg ICC_IGRPEN0_EL1 (Mk_ICC_IGRPEN0_EL1_Type w__46)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_IGRPEN1_EL1_SysRegWrite_a249f92f5cac95a3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_IRQ : (BitVec 1) := (_get_SCR_EL3_Type_IRQ w__2)
  let w__3 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_ICC_IGRPENn_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_ICC_IGRPENn_EL1 w__5)
  let w__6 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TALL1 : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TALL1 w__6)
  let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_IMO : (BitVec 1) := (_get_HCR_EL2_Type_IMO w__7)
  let w__8 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__8)
  let w__9 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__9)
  let w__10 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__10)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__17 ← (( do
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
                  else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM Bool )
          if (w__17 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__ICC_SRE_EL1_SRE == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__24 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__21 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__21) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HFGWTR_EL2_ICC_IGRPENn_EL1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__26 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__ICH_HCR_EL2_TALL1 == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__26 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__28 ← (( do
                            (pure ((← do
                                  (EL2Enabled ())) && ((__HCR_EL2_IMO == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__28 : Bool)
                          then
                            (do
                              let w__29 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ICV_IGRPEN1_EL1 (Mk_ICV_IGRPEN1_EL1_Type w__29))
                          else
                            (do
                              let w__31 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__31 : Bool)
                              then
                                (do
                                  let w__33 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__33 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__34 ← (( do (HaveEL EL3) ) : SailM Bool )
                                  if (w__34 : Bool)
                                  then
                                    (do
                                      if ((__SCR_EL3_NS == 0#1) : Bool)
                                      then
                                        (do
                                          let w__35 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                          writeReg ICC_IGRPEN1_EL1_S (Mk_ICC_IGRPEN1_EL1_Type w__35))
                                      else
                                        (do
                                          let w__36 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                          writeReg ICC_IGRPEN1_EL1_NS (Mk_ICC_IGRPEN1_EL1_Type w__36)))
                                  else
                                    (do
                                      let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      (ICC_IGRPEN1_EL1_write (Mk_ICC_IGRPEN1_EL1_Type w__37))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
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
                      else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM Bool )
              if (w__44 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__ICC_SRE_EL2_SRE == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__46 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM Bool )
                      if (w__46 : Bool)
                      then
                        (do
                          let w__48 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__48 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__49 ← (( do (HaveEL EL3) ) : SailM Bool )
                          if (w__49 : Bool)
                          then
                            (do
                              if ((__SCR_EL3_NS == 0#1) : Bool)
                              then
                                (do
                                  let w__50 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ICC_IGRPEN1_EL1_S (Mk_ICC_IGRPEN1_EL1_Type w__50))
                              else
                                (do
                                  let w__51 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg ICC_IGRPEN1_EL1_NS (Mk_ICC_IGRPEN1_EL1_Type w__51)))
                          else
                            (do
                              let w__52 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (ICC_IGRPEN1_EL1_write (Mk_ICC_IGRPEN1_EL1_Type w__52)))))))
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
                      if ((__SCR_EL3_NS == 0#1) : Bool)
                      then
                        (do
                          let w__53 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICC_IGRPEN1_EL1_S (Mk_ICC_IGRPEN1_EL1_Type w__53))
                      else
                        (do
                          let w__54 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg ICC_IGRPEN1_EL1_NS (Mk_ICC_IGRPEN1_EL1_Type w__54))))
              else (pure (())))))


end ArmFull.Functions
