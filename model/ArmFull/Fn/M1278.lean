import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0041
import ArmFull.Fn.M0046
import ArmFull.Fn.M0072
import ArmFull.Fn.M0073
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0112
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0184
import ArmFull.Fn.M0187
import ArmFull.Fn.M0203
import ArmFull.Fn.M0254
import ArmFull.Fn.M1174
import ArmFull.Fn.M1175

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

/-- Type quantifiers: offset : Int -/
def NVMem_read (offset : Int) : SailM (BitVec 64) := do
  ArmFull.assert (offset >b 0) "sail-arm/v8_base.sail:28757.21-28757.22"
  let size : Nat := 64
  ((Sail.BitVec.castWidth ) <$> (NVMem_read__1 offset size))


/-- Type quantifiers: offset : Int -/
def NVMem_set (offset : Int) (value_name : (BitVec 64)) : SailM Unit := do
  ArmFull.assert (offset >b 0) "sail-arm/v8_base.sail:28776.21-28776.22"
  let size : Nat := 64
  (NVMem_set__1 offset size (Sail.BitVec.castWidth value_name))


def GCSPUSHM (value_name : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (GCSEnabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  (AddGCSRecord value_name)


def GCSPUSHX (_ : Unit) : SailM Unit := do
  let spsr ← (( do (SPSR_read (N := 64)) ) : SailM (BitVec 64) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (GCSEnabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  let w__2 ← (( do (ELR_read__1 ()) ) : SailM (BitVec 64) )
  let w__3 ← (( do (X_read 30 64) ) : SailM (BitVec 64) )
  (AddGCSExRecord w__2 spsr w__3)
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with EXLOCK := 0#1 }


def GCSPOPCX (_ : Unit) : SailM Unit := do
  let spsr ← (( do (SPSR_read (N := 64)) ) : SailM (BitVec 64) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (GCSEnabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  let w__2 ← (( do (ELR_read__1 ()) ) : SailM (BitVec 64) )
  let w__3 ← (( do (X_read 30 64) ) : SailM (BitVec 64) )
  (CheckGCSExRecord w__2 spsr w__3 GCSInstType_POPCX)
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__5 ← (( do (GetCurrentEXLOCKEN ()) ) : SailM Bool )
  let w__6 : (BitVec 1) :=
    if (w__5 : Bool)
    then 1#1
    else 0#1
  writeReg PSTATE { w__4 with EXLOCK := w__6 }


/-- Type quantifiers: t : Int -/
def GCSPOPX_SysOpsWrite_f5624b6324bc7c49 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          (GCSPOPX ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              (GCSPOPX ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (GCSPOPX ()))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSPOPM_SysInstrWithResult_785f34ad5cd557fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do (GCSPOPM ()) ) : SailM (BitVec 64) )
      (X_set t 64 w__1))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__2 ← (( do (GCSPOPM ()) ) : SailM (BitVec 64) )
          (X_set t 64 w__2))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__3 ← (( do (GCSPOPM ()) ) : SailM (BitVec 64) )
              (X_set t 64 w__3))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__4 ← (( do (GCSPOPM ()) ) : SailM (BitVec 64) )
                  (X_set t 64 w__4))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSSS2_SysInstrWithResult_f9ffdfaa333b34bf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do (GCSSS2 ()) ) : SailM (BitVec 64) )
      (X_set t 64 w__1))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__2 ← (( do (GCSSS2 ()) ) : SailM (BitVec 64) )
          (X_set t 64 w__2))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__3 ← (( do (GCSSS2 ()) ) : SailM (BitVec 64) )
              (X_set t 64 w__3))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__4 ← (( do (GCSSS2 ()) ) : SailM (BitVec 64) )
                  (X_set t 64 w__4))
              else (pure (())))))


def AArch32_STC (coproc : (BitVec 4)) (CRd : (BitVec 4)) (address : (BitVec 32)) : SailM Unit := do
  if (((CRd == 0b0101#4) && (coproc == 0b1110#4)) : Bool)
  then
    (do
      (DBGDTRRXint_STC_521dc9133ebece9c coproc CRd address))
  else sailThrow ((Error_Undefined ()))


def AArch32_LDC (coproc : (BitVec 4)) (CRd : (BitVec 4)) (address : (BitVec 32)) : SailM Unit := do
  if (((CRd == 0b0101#4) && (coproc == 0b1110#4)) : Bool)
  then
    (do
      (DBGDTRTXint_LDC_da4baa792b999a1f coproc CRd address))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_EL1_SysRegRead128_e74a87d5451e7769 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TRVM : (BitVec 1) := (_get_HCR_EL2_Type_TRVM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_TTBR0_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_TTBR0_EL1 w__5)
  let w__6 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_D128En : (BitVec 1) := (_get_HCRX_EL2_Type_D128En w__6)
  let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__13 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__15 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TRVM == 1#1) : Bool))) ) : SailM Bool )
              if (w__15 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__20 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGRTR_EL2_TTBR0_EL1 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__20 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__24 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            (pure ((← do
                                  let w__22 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                  (pure (((! w__22) : Bool)))) || ((__HCRX_EL2_D128En == 0#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__24 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                          then
                            (do
                              let w__26 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__26 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                          else
                            (do
                              let w__31 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_NV2 w__28) +++ ((_get_HCR_EL2_Type_NV1
                                              w__29) +++ (_get_HCR_EL2_Type_NV w__30))) == 0b111#3) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__31 : Bool)
                              then
                                (do
                                  let w__32 ← (( do (NVMem_read__1 (BitVec.toNat 0x200#12) 128) )
                                    : SailM (BitVec 128) )
                                  let (__tup_0, __tup_1) ← (( do (Split w__32 64) ) : SailM
                                    ((BitVec 64) × (BitVec 64)) )
                                  (X_set (t +i 1) 64 __tup_0)
                                  (X_set t 64 __tup_1))
                              else
                                (do
                                  let w__33 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
                                  let (__tup_0, __tup_1) ← (( do (Split w__33 64) ) : SailM
                                    ((BitVec 64) × (BitVec 64)) )
                                  (X_set (t +i 1) 64 __tup_0)
                                  (X_set t 64 __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__39 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
              if (w__39 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      let w__41 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__41 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__42 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
                          let (__tup_0, __tup_1) ← (( do (Split w__42 64) ) : SailM
                            ((BitVec 64) × (BitVec 64)) )
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1))
                      else
                        (do
                          let w__43 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
                          let (__tup_0, __tup_1) ← (( do (Split w__43 64) ) : SailM
                            ((BitVec 64) × (BitVec 64)) )
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__44 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
                  let (__tup_0, __tup_1) ← (( do (Split w__44 64) ) : SailM
                    ((BitVec 64) × (BitVec 64)) )
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_EL1_SysRegRead128_ef7a13f49fb9674d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__6) +++ ((_get_HCR_EL2_Type_NV1 w__7) +++ (_get_HCR_EL2_Type_NV
                          w__8))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              let w__10 ← (( do (NVMem_read__1 (BitVec.toNat 0x200#12) 128) ) : SailM (BitVec 128)
                )
              let (__tup_0, __tup_1) ← (( do (Split w__10 64) ) : SailM
                ((BitVec 64) × (BitVec 64)) )
              (X_set (t +i 1) 64 __tup_0)
              (X_set t 64 __tup_1))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__18 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                      then
                        (do
                          let w__20 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__20 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          let w__21 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
                          let (__tup_0, __tup_1) ← (( do (Split w__21 64) ) : SailM
                            ((BitVec 64) × (BitVec 64)) )
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1))))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__25 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__23 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__23) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__25 : Bool)
                  then
                    (do
                      let w__26 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
                      let (__tup_0, __tup_1) ← (( do (Split w__26 64) ) : SailM
                        ((BitVec 64) × (BitVec 64)) )
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_EL1_SysRegRead128_16388106e031d578 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__6) +++ ((_get_HCR_EL2_Type_NV1 w__7) +++ (_get_HCR_EL2_Type_NV
                          w__8))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              let w__10 ← (( do (NVMem_read__1 (BitVec.toNat 0x210#12) 128) ) : SailM (BitVec 128)
                )
              let (__tup_0, __tup_1) ← (( do (Split w__10 64) ) : SailM
                ((BitVec 64) × (BitVec 64)) )
              (X_set (t +i 1) 64 __tup_0)
              (X_set t 64 __tup_1))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__18 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                      then
                        (do
                          let w__20 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__20 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          let w__21 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                          let (__tup_0, __tup_1) ← (( do (Split w__21 64) ) : SailM
                            ((BitVec 64) × (BitVec 64)) )
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1))))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__25 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__23 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__23) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__25 : Bool)
                  then
                    (do
                      let w__26 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                      let (__tup_0, __tup_1) ← (( do (Split w__26 64) ) : SailM
                        ((BitVec 64) × (BitVec 64)) )
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_EL2_SysRegRead128_ae708511fcb38e92 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TRVM : (BitVec 1) := (_get_HCR_EL2_Type_TRVM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_TTBR1_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_TTBR1_EL1 w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__12 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__14 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TRVM == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGRTR_EL2_TTBR1_EL1 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                      then
                        (do
                          let w__21 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__21 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          let w__26 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_NV2 w__23) +++ ((_get_HCR_EL2_Type_NV1
                                          w__24) +++ (_get_HCR_EL2_Type_NV w__25))) == 0b111#3) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__26 : Bool)
                          then
                            (do
                              let w__27 ← (( do (NVMem_read__1 (BitVec.toNat 0x210#12) 128) ) :
                                SailM (BitVec 128) )
                              let (__tup_0, __tup_1) ← (( do (Split w__27 64) ) : SailM
                                ((BitVec 64) × (BitVec 64)) )
                              (X_set (t +i 1) 64 __tup_0)
                              (X_set t 64 __tup_1))
                          else
                            (do
                              let w__28 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                              let (__tup_0, __tup_1) ← (( do (Split w__28 64) ) : SailM
                                ((BitVec 64) × (BitVec 64)) )
                              (X_set (t +i 1) 64 __tup_0)
                              (X_set t 64 __tup_1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__34 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
              if (w__34 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_D128En == 0#1)) : Bool)
                  then
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__36 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__37 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
                          let (__tup_0, __tup_1) ← (( do (Split w__37 64) ) : SailM
                            ((BitVec 64) × (BitVec 64)) )
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1))
                      else
                        (do
                          let w__38 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                          let (__tup_0, __tup_1) ← (( do (Split w__38 64) ) : SailM
                            ((BitVec 64) × (BitVec 64)) )
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__39 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                  let (__tup_0, __tup_1) ← (( do (Split w__39 64) ) : SailM
                    ((BitVec 64) × (BitVec 64)) )
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure (())))))


end ArmFull.Functions
