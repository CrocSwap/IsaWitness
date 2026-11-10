import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0035
import ArmFull.Fn.M0036
import ArmFull.Fn.M0064
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0144
import ArmFull.Fn.M0166
import ArmFull.Fn.M0181
import ArmFull.Fn.M0254

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
def BRBSRC_EL1_SysRegRead_33c4b2eee9151575 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__12 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             (pure ((← do
                                   (pure ((← do
                                         (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                        then
                          (do
                            (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                        else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__19 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (pure ((← do
                                       (pure ((← do
                                             (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                            then
                              (do
                                (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                            else (pure false)) && (let b__3 := __MDCR_EL3_SBRBE
                          (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 0 0)) == (0#1 : (BitVec 1))) : Bool)
                          then true
                          else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__19 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__24 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGRTR_EL2_nBRBDATA == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          let w__26 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__26 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__2 := __MDCR_EL3_SBRBE
                                 (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2
                                        0 0)) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool))) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              let w__28 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__28 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__29 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                              if (((31 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__29)) *i 32)) ≥b 64) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__30 ← (( do readReg BRBSRC_EL1 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  (X_set t 64 (GetElem?.getElem! w__30 31)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__37 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (pure ((← do
                                       (pure ((← do
                                             (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                            then
                              (do
                                (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                            else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__37 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (pure ((← do
                                           (pure ((← do
                                                 (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                                then
                                  (do
                                    (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                else (pure false)) && (let b__1 := __MDCR_EL3_SBRBE
                              (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
                              then true
                              else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__44 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
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
                          if ((((HaveEL EL3) && (let b__0 := __MDCR_EL3_SBRBE
                                 (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0
                                        0 0)) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool))) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              let w__48 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__48 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__49 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                              if (((31 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__49)) *i 32)) ≥b 64) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__50 ← (( do readReg BRBSRC_EL1 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  (X_set t 64 (GetElem?.getElem! w__50 31))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__51 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                  if (((31 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__51)) *i 32)) ≥b 64) : Bool)
                  then
                    (do
                      (X_set t 64 (Zeros (n := 64))))
                  else
                    (do
                      let w__52 ← (( do readReg BRBSRC_EL1 ) : SailM (Vector (BitVec 64) 32) )
                      (X_set t 64 (GetElem?.getElem! w__52 31))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_3ce62e599c7c836c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__12 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             (pure ((← do
                                   (pure ((← do
                                         (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                        then
                          (do
                            (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                        else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__19 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (pure ((← do
                                       (pure ((← do
                                             (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                            then
                              (do
                                (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                            else (pure false)) && (let b__3 := __MDCR_EL3_SBRBE
                          (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 0 0)) == (0#1 : (BitVec 1))) : Bool)
                          then true
                          else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__19 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__24 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGRTR_EL2_nBRBDATA == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          let w__26 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__26 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__2 := __MDCR_EL3_SBRBE
                                 (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2
                                        0 0)) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool))) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              let w__28 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__28 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__29 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                              if (((19 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__29)) *i 32)) ≥b 64) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__30 ← (( do readReg BRBSRC_EL1 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  (X_set t 64 (GetElem?.getElem! w__30 19)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__37 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (pure ((← do
                                       (pure ((← do
                                             (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                            then
                              (do
                                (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                            else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__37 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (pure ((← do
                                           (pure ((← do
                                                 (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                                then
                                  (do
                                    (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                else (pure false)) && (let b__1 := __MDCR_EL3_SBRBE
                              (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
                              then true
                              else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__44 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
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
                          if ((((HaveEL EL3) && (let b__0 := __MDCR_EL3_SBRBE
                                 (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0
                                        0 0)) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool))) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              let w__48 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__48 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__49 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                              if (((19 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__49)) *i 32)) ≥b 64) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__50 ← (( do readReg BRBSRC_EL1 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  (X_set t 64 (GetElem?.getElem! w__50 19))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__51 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                  if (((19 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__51)) *i 32)) ≥b 64) : Bool)
                  then
                    (do
                      (X_set t 64 (Zeros (n := 64))))
                  else
                    (do
                      let w__52 ← (( do readReg BRBSRC_EL1 ) : SailM (Vector (BitVec 64) 32) )
                      (X_set t 64 (GetElem?.getElem! w__52 19))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def BRBSRC_EL1_SysRegRead_42de11a512022e40 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__12 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             (pure ((← do
                                   (pure ((← do
                                         (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                        then
                          (do
                            (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                        else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__19 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (pure ((← do
                                       (pure ((← do
                                             (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                            then
                              (do
                                (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                            else (pure false)) && (let b__3 := __MDCR_EL3_SBRBE
                          (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 0 0)) == (0#1 : (BitVec 1))) : Bool)
                          then true
                          else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__19 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__24 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGRTR_EL2_nBRBDATA == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          let w__26 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__26 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__2 := __MDCR_EL3_SBRBE
                                 (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2
                                        0 0)) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool))) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              let w__28 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__28 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__29 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                              if (((18 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__29)) *i 32)) ≥b 64) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__30 ← (( do readReg BRBSRC_EL1 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  (X_set t 64 (GetElem?.getElem! w__30 18)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__37 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (pure ((← do
                                       (pure ((← do
                                             (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                            then
                              (do
                                (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                            else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__37 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (pure ((← do
                                           (pure ((← do
                                                 (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                                then
                                  (do
                                    (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                else (pure false)) && (let b__1 := __MDCR_EL3_SBRBE
                              (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
                              then true
                              else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__44 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
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
                          if ((((HaveEL EL3) && (let b__0 := __MDCR_EL3_SBRBE
                                 (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0
                                        0 0)) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool))) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              let w__48 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__48 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__49 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                              if (((18 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__49)) *i 32)) ≥b 64) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__50 ← (( do readReg BRBSRC_EL1 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  (X_set t 64 (GetElem?.getElem! w__50 18))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__51 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
                  if (((18 +i ((BitVec.toNat (_get_BRBFCR_EL1_Type_BANK w__51)) *i 32)) ≥b 64) : Bool)
                  then
                    (do
                      (X_set t 64 (Zeros (n := 64))))
                  else
                    (do
                      let w__52 ← (( do readReg BRBSRC_EL1 ) : SailM (Vector (BitVec 64) 32) )
                      (X_set t 64 (GetElem?.getElem! w__52 18))))
              else (pure (())))))


end ArmFull.Functions
