module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0075
public import ArmFull.Fn.M0079
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0195
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
def CNTHVS_CVAL_EL2_SysRegWrite_5acd4d20ee782a13 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
          if ((! w__3) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__5 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__5 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__6 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
              if ((! w__6) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type w__7)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type w__8)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHVS_TVAL_EL2_SysRegWrite_e71ca762af073cad (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
          if ((! w__3) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__5 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__5 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__6 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
              if ((! w__6) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let w__8 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type
                    ((Sail.BitVec.castWidth (m := 64) (sign_extend
                        (Sail.BitVec.extractLsb w__7 31 0) 64)) + w__8))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      let w__10 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type
                        ((Sail.BitVec.castWidth (m := 64) (sign_extend
                            (Sail.BitVec.extractLsb w__9 31 0) 64)) + w__10))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHV_CTL_EL2_SysRegWrite_33f75e4b41646088 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (__set_CNTHV_CTL_EL2 (Mk_CNTHV_CTL_EL2_Type w__4)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (__set_CNTHV_CTL_EL2 (Mk_CNTHV_CTL_EL2_Type w__5)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHV_CVAL_EL2_SysRegWrite_a0eabf75b26da37c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type w__4))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHV_TVAL_EL2_SysRegWrite_6e74ff633c511335 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              let w__5 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
              writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type
                ((Sail.BitVec.castWidth (m := 64) (sign_extend (Sail.BitVec.extractLsb w__4 31 0) 64)) + w__5)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let w__7 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type
                    ((Sail.BitVec.castWidth (m := 64) (sign_extend
                        (Sail.BitVec.extractLsb w__6 31 0) 64)) + w__7)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHV_TVAL_EL2_SysRegWrite_b6bfac5d17f766fc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0VTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0VTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0VTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0VTEN w__3)
  let w__4 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1TVT : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1TVT w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__9 ← (( do
        (pure ((← do
              let w__8 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__6) +++ (_get_HCR_EL2_Type_TGE w__7)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__8) : Bool)))) && ((__CNTKCTL_EL1_EL0VTEN == 0#1) : Bool))) ) : SailM
        Bool )
      if (w__9 : Bool)
      then
        (do
          let w__11 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__13) +++ (_get_HCR_EL2_Type_TGE w__14)) == 0b11#2) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL0VTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__21 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__18) +++ (_get_HCR_EL2_Type_TGE w__19)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__21 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__29 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__23) +++ (_get_HCR_EL2_Type_TGE
                                          w__24)) == 0b11#2) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             let w__26 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((_get_SCR_EL3_Type_NS w__26) == 0#1) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        (IsFeatureImplemented FEAT_SEL2))
                    else (pure false) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      let w__30 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      let w__31 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type
                        ((Sail.BitVec.castWidth (m := 64) (sign_extend
                            (Sail.BitVec.extractLsb w__30 31 0) 64)) + w__31)))
                  else
                    (do
                      let w__37 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 let w__34 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure (((((_get_HCR_EL2_Type_E2H w__33) +++ (_get_HCR_EL2_Type_TGE
                                         w__34)) == 0b11#2) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__36 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure ((((_get_SCR_EL3_Type_NS w__36) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__37 : Bool)
                      then
                        (do
                          let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          let w__39 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type
                            ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                (Sail.BitVec.extractLsb w__38 31 0) 64)) + w__39)))
                      else
                        (do
                          let w__45 ← (( do
                            if ((← do
                                 (HaveEL EL2)) : Bool)
                            then
                              (do
                                if ((← do
                                     let w__41 ← (( do (EL2Enabled ()) ) : SailM Bool )
                                     (pure (((! w__41) : Bool)))) : Bool)
                                then (pure true)
                                else
                                  (do
                                    let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__42) +++ (_get_HCR_EL2_Type_TGE
                                            w__43)) != 0b11#2) : Bool)))))
                            else (pure false) ) : SailM Bool )
                          if (w__45 : Bool)
                          then
                            (do
                              let w__46 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              let w__47 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              let w__48 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                              writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type
                                ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                      (Sail.BitVec.extractLsb w__46 31 0) 64)) + w__47)) - w__48)))
                          else
                            (do
                              let w__49 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              let w__50 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type
                                ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                    (Sail.BitVec.extractLsb w__49 31 0) 64)) + w__50)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__52 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool )
          if (w__52 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__53 ← (( do (HaveEL EL2) ) : SailM Bool )
              if (w__53 : Bool)
              then
                (do
                  let w__54 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let w__55 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  let w__56 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                  writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type
                    ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                          (Sail.BitVec.extractLsb w__54 31 0) 64)) + w__55)) - w__56)))
              else
                (do
                  let w__57 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let w__58 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type
                    ((Sail.BitVec.castWidth (m := 64) (sign_extend
                        (Sail.BitVec.extractLsb w__57 31 0) 64)) + w__58)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__63 ← (( do
                if ((← do
                     if ((← do
                          let w__59 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_E2H w__59) == 1#1) : Bool)))) : Bool)
                     then
                       (do
                         let w__60 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_SCR_EL3_Type_NS w__60) == 0#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    (IsFeatureImplemented FEAT_SEL2))
                else (pure false) ) : SailM Bool )
              if (w__63 : Bool)
              then
                (do
                  let w__64 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let w__65 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  writeReg CNTHVS_CVAL_EL2 (Mk_CNTHVS_CVAL_EL2_Type
                    ((Sail.BitVec.castWidth (m := 64) (sign_extend
                        (Sail.BitVec.extractLsb w__64 31 0) 64)) + w__65)))
              else
                (do
                  let w__68 ← (( do
                    if ((← do
                         let w__66 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         (pure ((((_get_HCR_EL2_Type_E2H w__66) == 1#1) : Bool)))) : Bool)
                    then
                      (do
                        let w__67 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        (pure ((((_get_SCR_EL3_Type_NS w__67) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__68 : Bool)
                  then
                    (do
                      let w__69 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      let w__70 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      writeReg CNTHV_CVAL_EL2 (Mk_CNTHV_CVAL_EL2_Type
                        ((Sail.BitVec.castWidth (m := 64) (sign_extend
                            (Sail.BitVec.extractLsb w__69 31 0) 64)) + w__70)))
                  else
                    (do
                      let w__71 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      if (((_get_HCR_EL2_Type_E2H w__71) == 0#1) : Bool)
                      then
                        (do
                          let w__72 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          let w__73 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          let w__74 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                          writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type
                            ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                  (Sail.BitVec.extractLsb w__72 31 0) 64)) + w__73)) - w__74)))
                      else
                        (do
                          let w__75 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          let w__76 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type
                            ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                (Sail.BitVec.extractLsb w__75 31 0) 64)) + w__76))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__79 ← (( do
                    if ((← do
                         (HaveEL EL2)) : Bool)
                    then
                      (do
                        let w__78 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                        (pure (((! w__78) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__79 : Bool)
                  then
                    (do
                      let w__80 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      let w__81 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__82 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                      writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type
                        ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                              (Sail.BitVec.extractLsb w__80 31 0) 64)) + w__81)) - w__82)))
                  else
                    (do
                      let w__85 ← (( do
                        if ((← do
                             (HaveEL EL2)) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL2))
                        else (pure false) ) : SailM Bool )
                      if (w__85 : Bool)
                      then
                        (do
                          let w__86 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          let w__87 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          let w__88 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                          writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type
                            ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                  (Sail.BitVec.extractLsb w__86 31 0) 64)) + w__87)) - w__88)))
                      else
                        (do
                          let w__89 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          let w__90 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          writeReg CNTV_CVAL_EL0 (Mk_CNTV_CVAL_EL0_Type
                            ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                (Sail.BitVec.extractLsb w__89 31 0) 64)) + w__90)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTKCTL_EL1_SysRegWrite_b6b89671d5078ba5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__4 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type w__5))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
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
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type w__10))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTPS_CTL_EL1_SysRegWrite_22bfd6d865a619e7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ST : (BitVec 1) := (_get_SCR_EL3_Type_ST w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (HaveEL EL3)) && ((__SCR_EL3_NS == 0#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              if ((__SCR_EL3_EEL2 == 1#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__SCR_EL3_ST == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (__set_CNTPS_CTL_EL1 (Mk_CNTPS_CTL_EL1_Type w__6)))))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (__set_CNTPS_CTL_EL1 (Mk_CNTPS_CTL_EL1_Type w__7)))
              else (pure (())))))


end ArmFull.Functions
