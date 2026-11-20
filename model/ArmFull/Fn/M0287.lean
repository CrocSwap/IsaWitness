module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0065
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
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
def BRBINF_EL1_SysRegRead_e899a449a42d0451 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              let w__39 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                              if (((2 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__39)) *i 32)) ≥b 64) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__40 ← (( do readReg BRBINF_EL1 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! w__40 2))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__48 ← (( do
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
              if (w__48 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__56 ← (( do
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
                  if (w__56 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__59 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (HaveEL EL3)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                        ) : SailM Bool )
                      if (w__59 : Bool)
                      then
                        (do
                          let w__61 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__61 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__64 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        (HaveEL EL3)) && (let b__0 := __MDCR_EL3_SBRBE
                                      (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                                      then true
                                      else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__64 : Bool)
                          then
                            (do
                              let w__66 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__66 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__67 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                              if (((2 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__67)) *i 32)) ≥b 64) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__68 ← (( do readReg BRBINF_EL1 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! w__68 2)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__69 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                  if (((2 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__69)) *i 32)) ≥b 64) : Bool)
                  then
                    (do
                      (X_set t 64 (Zeros (n := 64))))
                  else
                    (do
                      let w__70 ← (( do readReg BRBINF_EL1 ) : SailM (Vector (BitVec 64) 32) )
                      (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! w__70 2)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_ea333ab47e4a6f1e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              let w__39 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                              if (((28 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__39)) *i 32)) ≥b 64) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__40 ← (( do readReg BRBINF_EL1 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! w__40 28))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__48 ← (( do
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
              if (w__48 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__56 ← (( do
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
                  if (w__56 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__59 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (HaveEL EL3)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                        ) : SailM Bool )
                      if (w__59 : Bool)
                      then
                        (do
                          let w__61 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__61 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__64 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        (HaveEL EL3)) && (let b__0 := __MDCR_EL3_SBRBE
                                      (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                                      then true
                                      else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__64 : Bool)
                          then
                            (do
                              let w__66 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__66 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__67 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                              if (((28 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__67)) *i 32)) ≥b 64) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__68 ← (( do readReg BRBINF_EL1 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! w__68 28)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__69 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                  if (((28 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__69)) *i 32)) ≥b 64) : Bool)
                  then
                    (do
                      (X_set t 64 (Zeros (n := 64))))
                  else
                    (do
                      let w__70 ← (( do readReg BRBINF_EL1 ) : SailM (Vector (BitVec 64) 32) )
                      (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! w__70 28)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def BRBINF_EL1_SysRegRead_ecdadc5359d94302 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                              let w__39 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                              if (((0 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__39)) *i 32)) ≥b 64) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__40 ← (( do readReg BRBINF_EL1 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! w__40 0))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__48 ← (( do
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
              if (w__48 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__56 ← (( do
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
                  if (w__56 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__59 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (HaveEL EL3)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                        ) : SailM Bool )
                      if (w__59 : Bool)
                      then
                        (do
                          let w__61 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__61 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__64 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        (HaveEL EL3)) && (let b__0 := __MDCR_EL3_SBRBE
                                      (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                                      then true
                                      else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__64 : Bool)
                          then
                            (do
                              let w__66 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__66 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__67 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                              if (((0 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__67)) *i 32)) ≥b 64) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__68 ← (( do readReg BRBINF_EL1 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! w__68 0)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__69 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                  if (((0 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__69)) *i 32)) ≥b 64) : Bool)
                  then
                    (do
                      (X_set t 64 (Zeros (n := 64))))
                  else
                    (do
                      let w__70 ← (( do readReg BRBINF_EL1 ) : SailM (Vector (BitVec 64) 32) )
                      (X_set t 64 (__get_BRBINF_EL1 (GetElem?.getElem! w__70 0)))))
              else (pure (())))))


end ArmFull.Functions
