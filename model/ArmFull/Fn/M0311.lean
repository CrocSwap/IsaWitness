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
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0065
public import ArmFull.Fn.M0076
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0139
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
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
def BRBTS_EL1_SysRegRead_a92810602a111e63 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_SBRBE : (BitVec 2) := (_get_MDCR_EL3_Type_SBRBE w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_nBRBDATA : (BitVec 1) := (_get_HDFGRTR_EL2_Type_nBRBDATA w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__13 ← (( do
            (pure ((← do
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
                        else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__21 ← (( do
                (pure ((← do
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
                            else (pure false)) && (let b__3 := __MDCR_EL3_SBRBE
                          (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 0 0)) == (0#1 : (BitVec 1))) : Bool)
                          then true
                          else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__21 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__28 ← (( do
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
                                    let w__25 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__25) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGRTR_EL2_nBRBDATA == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__28 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__31 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (HaveEL EL3)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                        ) : SailM Bool )
                      if (w__31 : Bool)
                      then
                        (do
                          let w__33 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__33 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__36 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        (HaveEL EL3)) && (let b__2 := __MDCR_EL3_SBRBE
                                      (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__2 0 0)) == (0#1 : (BitVec 1))) : Bool)
                                      then true
                                      else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__36 : Bool)
                          then
                            (do
                              let w__38 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__38 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__39 ← (( do readReg BRBTS_EL1 ) : SailM (BitVec 64) )
                              (X_set t 64 w__39)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__47 ← (( do
                (pure ((← do
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
                            else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__47 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__55 ← (( do
                    (pure ((← do
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
                                else (pure false)) && (let b__1 := __MDCR_EL3_SBRBE
                              (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
                              then true
                              else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__55 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__58 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (HaveEL EL3)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                        ) : SailM Bool )
                      if (w__58 : Bool)
                      then
                        (do
                          let w__60 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__60 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__63 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        (HaveEL EL3)) && (let b__0 := __MDCR_EL3_SBRBE
                                      (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                                      then true
                                      else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__63 : Bool)
                          then
                            (do
                              let w__65 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__65 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__66 ← (( do readReg BRBTS_EL1 ) : SailM (BitVec 64) )
                              (X_set t 64 w__66))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__67 ← (( do readReg BRBTS_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 w__67))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CCSIDR2_EL1_SysRegRead_7161997c851583ee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID2 : (BitVec 1) := (_get_HCR_EL2_Type_TID2 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID4 : (BitVec 1) := (_get_HCR_EL2_Type_TID4 w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__4 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else sailThrow ((Error_Undefined ())))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID2 == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TID4 == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__11 ← (( do readReg CCSIDR2_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CCSIDR2_EL1 w__11)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do readReg CCSIDR2_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_CCSIDR2_EL1 w__12)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do readReg CCSIDR2_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CCSIDR2_EL1 w__13)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CCSIDR_EL1_SysRegRead_5f1582fb2f446af0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID2 : (BitVec 1) := (_get_HCR_EL2_Type_TID2 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID4 : (BitVec 1) := (_get_HCR_EL2_Type_TID4 w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_CCSIDR_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_CCSIDR_EL1 w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__6 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__6 : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else sailThrow ((Error_Undefined ())))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID2 == 1#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TID4 == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__19 ← (( do
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
                                    let w__16 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__16) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HFGRTR_EL2_CCSIDR_EL1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__20 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CCSIDR_EL1 w__20))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__21 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_CCSIDR_EL1 w__21)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__22 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CCSIDR_EL1 w__22)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CLIDR_EL1_SysRegRead_e5c2643fd321419d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID2 : (BitVec 1) := (_get_HCR_EL2_Type_TID2 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID4 : (BitVec 1) := (_get_HCR_EL2_Type_TID4 w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_CLIDR_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_CLIDR_EL1 w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__6 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__6 : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else sailThrow ((Error_Undefined ())))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID2 == 1#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TID4 == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__19 ← (( do
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
                                    let w__16 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__16) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HFGRTR_EL2_CLIDR_EL1 == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__20 ← (( do readReg CLIDR_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CLIDR_EL1 w__20))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__21 ← (( do readReg CLIDR_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_CLIDR_EL1 w__21)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__22 ← (( do readReg CLIDR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CLIDR_EL1 w__22)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTFRQ_EL0_SysRegRead_aed619ec0d882dc5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__8 ← (( do
        if ((← do
             let w__5 ← (( do
               if ((← do
                    (EL2Enabled ())) : Bool)
               then
                 (do
                   let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure (((((_get_HCR_EL2_Type_E2H w__3) +++ (_get_HCR_EL2_Type_TGE w__4)) == 0b11#2) : Bool))))
               else (pure false) ) : SailM Bool )
             (pure (((! w__5) : Bool)))) : Bool)
        then
          (do
            let w__6 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
            let w__7 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
            (pure (((((_get_CNTKCTL_EL1_Type_EL0PCTEN w__6) +++ (_get_CNTKCTL_EL1_Type_EL0VCTEN w__7)) == 0b00#2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__17 ← (( do
            if ((← do
                 if ((← do
                      (EL2Enabled ())) : Bool)
                 then
                   (do
                     let w__12 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     (pure (((((_get_HCR_EL2_Type_E2H w__12) +++ (_get_HCR_EL2_Type_TGE w__13)) == 0b11#2) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__15 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                let w__16 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_CNTHCTL_EL2_Type_EL0PCTEN w__15) +++ (_get_CNTHCTL_EL2_Type_EL0VCTEN
                        w__16)) == 0b00#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__17 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__18 ← (( do readReg CNTFRQ_EL0 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_CNTFRQ_EL0 w__18)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__19 ← (( do readReg CNTFRQ_EL0 ) : SailM (BitVec 64) )
          (X_set t 64 (__get_CNTFRQ_EL0 w__19)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__20 ← (( do readReg CNTFRQ_EL0 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_CNTFRQ_EL0 w__20)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__21 ← (( do readReg CNTFRQ_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTFRQ_EL0 w__21)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHCTL_EL2_SysRegRead_25bfe781a33503e5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_CNTHCTL_EL2 w__4)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTHCTL_EL2 w__5)))
              else (pure (())))))


end ArmFull.Functions
