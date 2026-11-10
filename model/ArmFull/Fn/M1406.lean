import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0042
import ArmFull.Fn.M0052
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0112
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0181
import ArmFull.Fn.M0253
import ArmFull.Fn.M0254
import ArmFull.Fn.M0432
import ArmFull.Fn.M0560
import ArmFull.Fn.M0561
import ArmFull.Fn.M0562
import ArmFull.Fn.M1278
import ArmFull.Fn.M1279
import ArmFull.Fn.M1280
import ArmFull.Fn.M1291

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
def GCSPOPCX_SysOpsWrite_8b33b35a7177cc05 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EXLOCK : (BitVec 1) := w__1.EXLOCK
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_nGCSEPP : (BitVec 1) := (_get_HFGITR_EL2_Type_nGCSEPP w__3)
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
                       if ((← do
                            (IsFeatureImplemented FEAT_GCS)) : Bool)
                       then
                         (do
                           (GetCurrentEXLOCKEN ()))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__7 ← (( do (Halted ()) ) : SailM Bool )
                      (pure (((! w__7) : Bool))))
                  else (pure false)) && ((__PSTATE_EXLOCK == 1#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (EXLOCKException ()))
          else
            (do
              let w__14 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_nGCSEPP == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (GCSPOPCX ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__20 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (IsFeatureImplemented FEAT_GCS)) : Bool)
                           then
                             (do
                               (GetCurrentEXLOCKEN ()))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__18 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__18) : Bool))))
                      else (pure false)) && ((__PSTATE_EXLOCK == 1#1) : Bool))) ) : SailM Bool )
              if (w__20 : Bool)
              then
                (do
                  (EXLOCKException ()))
              else
                (do
                  (GCSPOPCX ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__26 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (IsFeatureImplemented FEAT_GCS)) : Bool)
                               then
                                 (do
                                   (GetCurrentEXLOCKEN ()))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__24 ← (( do (Halted ()) ) : SailM Bool )
                              (pure (((! w__24) : Bool))))
                          else (pure false)) && ((__PSTATE_EXLOCK == 1#1) : Bool))) ) : SailM Bool )
                  if (w__26 : Bool)
                  then
                    (do
                      (EXLOCKException ()))
                  else
                    (do
                      (GCSPOPCX ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSPUSHM_SysOpsWrite_7d31b427953fb1be (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  let __GCSCRE0_EL1_PUSHMEn : (BitVec 1) := (_get_GCSCRE0_EL1_Type_PUSHMEn w__2)
  let w__3 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  let __GCSCR_EL1_PUSHMEn : (BitVec 1) := (_get_GCSCR_EL1_Type_PUSHMEn w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_nGCSPUSHM_EL1 : (BitVec 1) := (_get_HFGITR_EL2_Type_nGCSPUSHM_EL1 w__5)
  let w__6 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  let __GCSCR_EL2_PUSHMEn : (BitVec 1) := (_get_GCSCR_EL2_Type_PUSHMEn w__6)
  let w__7 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  let __GCSCR_EL3_PUSHMEn : (BitVec 1) := (_get_GCSCR_EL3_Type_PUSHMEn w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__10 ← (( do
        (pure ((← do
              (pure ((← do
                    let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                    (pure (((! w__8) : Bool)))) || ((__HCR_EL2_TGE != 1#1) : Bool)))) && ((__GCSCRE0_EL1_PUSHMEn == 0#1) : Bool)))
        ) : SailM Bool )
      if (w__10 : Bool)
      then
        (do
          (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else
        (do
          let w__13 ← (( do
            (pure ((← do
                  (pure ((← do
                        (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool)))) && ((__GCSCRE0_EL1_PUSHMEn == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (GCSPUSHM w__14))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((__GCSCR_EL1_PUSHMEn == 0#1) : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
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
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_nGCSPUSHM_EL1 == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__19 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (GCSPUSHM w__20))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__GCSCR_EL2_PUSHMEn == 0#1) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__21 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (GCSPUSHM w__21)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__GCSCR_EL3_PUSHMEn == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__22 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (GCSPUSHM w__22)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSPUSHX_SysOpsWrite_c023a281d843c45a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EXLOCK : (BitVec 1) := w__1.EXLOCK
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_nGCSEPP : (BitVec 1) := (_get_HFGITR_EL2_Type_nGCSEPP w__3)
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
                       if ((← do
                            (IsFeatureImplemented FEAT_GCS)) : Bool)
                       then
                         (do
                           (GetCurrentEXLOCKEN ()))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__7 ← (( do (Halted ()) ) : SailM Bool )
                      (pure (((! w__7) : Bool))))
                  else (pure false)) && ((__PSTATE_EXLOCK == 0#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (EXLOCKException ()))
          else
            (do
              let w__14 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_nGCSEPP == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (GCSPUSHX ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__20 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (IsFeatureImplemented FEAT_GCS)) : Bool)
                           then
                             (do
                               (GetCurrentEXLOCKEN ()))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__18 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__18) : Bool))))
                      else (pure false)) && ((__PSTATE_EXLOCK == 0#1) : Bool))) ) : SailM Bool )
              if (w__20 : Bool)
              then
                (do
                  (EXLOCKException ()))
              else
                (do
                  (GCSPUSHX ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__26 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (IsFeatureImplemented FEAT_GCS)) : Bool)
                               then
                                 (do
                                   (GetCurrentEXLOCKEN ()))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__24 ← (( do (Halted ()) ) : SailM Bool )
                              (pure (((! w__24) : Bool))))
                          else (pure false)) && ((__PSTATE_EXLOCK == 0#1) : Bool))) ) : SailM Bool )
                  if (w__26 : Bool)
                  then
                    (do
                      (EXLOCKException ()))
                  else
                    (do
                      (GCSPUSHX ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AArch64_AutoGen_SysInstrWithResult (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  if ((((((CRm == 0b0111#4) && (CRn == 0b0111#4)) && (op0 == 0b01#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
  then
    (do
      (GCSSS2_SysInstrWithResult_f9ffdfaa333b34bf el op0 op1 CRn op2 CRm t))
  else
    (do
      if ((((((CRm == 0b0111#4) && (CRn == 0b0111#4)) && (op0 == 0b01#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
      then
        (do
          (GCSPOPM_SysInstrWithResult_785f34ad5cd557fe el op0 op1 CRn op2 CRm t))
      else
        (do
          (AArch64_UnallocatedSysRegAccess op0 op1 CRn op2 CRm false t)))


/-- Type quantifiers: t : Int, t2 : Int -/
def AArch64_AutoGen_SysRegRead128 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  if ((((((CRm == 0b0100#4) && (CRn == 0b0111#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
  then
    (do
      (PAR_EL1_SysRegRead128_8206ac7c9b0eef57 el op0 op1 CRn op2 CRm t t2))
  else
    (do
      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
      then
        (do
          (RCWSMASK_EL1_SysRegRead128_7cac5e35b1fae5f9 el op0 op1 CRn op2 CRm t t2))
      else
        (do
          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
          then
            (do
              (TTBR1_EL2_SysRegRead128_ae708511fcb38e92 el op0 op1 CRn op2 CRm t t2))
          else
            (do
              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
              then
                (do
                  (TTBR1_EL1_SysRegRead128_16388106e031d578 el op0 op1 CRn op2 CRm t t2))
              else
                (do
                  if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                  then
                    (do
                      (TTBR0_EL2_SysRegRead128_05dc18b820cc86b7 el op0 op1 CRn op2 CRm t t2))
                  else
                    (do
                      if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                      then
                        (do
                          (TTBR0_EL1_SysRegRead128_e74a87d5451e7769 el op0 op1 CRn op2 CRm t t2))
                      else
                        (do
                          if ((((((CRm == 0b0001#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                          then
                            (do
                              (VTTBR_EL2_SysRegRead128_a9b3226c12a0e07e el op0 op1 CRn op2 CRm t t2))
                          else
                            (do
                              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                              then
                                (do
                                  (TTBR0_EL1_SysRegRead128_ef7a13f49fb9674d el op0 op1 CRn op2 CRm t
                                    t2))
                              else
                                (do
                                  if ((((((match CRm with
                                             | b__0 => true : Bool) && (let b__1 := CRn
                                             (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                      b__1 3 3)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                      b__1 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                                             then true
                                             else false : Bool))) && (op0 == 0b11#2)) && (match op1 with
                                         | b__2 => true : Bool)) && (match op2 with
                                       | b__3 => true : Bool)) : Bool)
                                  then
                                    (do
                                      (S3_op1_Cn_Cm_op2_SysRegRead128_6403c05d5d1898d5 el op0 op1
                                        CRn op2 CRm t t2))
                                  else
                                    (do
                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                      then
                                        (do
                                          (RCWMASK_EL1_SysRegRead128_7c7466f3a5148cfe el op0 op1 CRn
                                            op2 CRm t t2))
                                      else
                                        (do
                                          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                          then
                                            (do
                                              (TTBR1_EL2_SysRegRead128_712360e50061655a el op0 op1
                                                CRn op2 CRm t t2))
                                          else
                                            (do
                                              (AArch64_UnallocatedSysRegAccess op0 op1 CRn op2 CRm
                                                true t))))))))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AArch64_AutoGen_SysRegWrite128 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  if ((((((CRm == 0b0100#4) && (CRn == 0b0111#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
  then
    (do
      (PAR_EL1_SysRegWrite128_e67f3244d494abe6 el op0 op1 CRn op2 CRm t t2))
  else
    (do
      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
      then
        (do
          (RCWSMASK_EL1_SysRegWrite128_d70b97b0479af313 el op0 op1 CRn op2 CRm t t2))
      else
        (do
          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
          then
            (do
              (TTBR1_EL2_SysRegWrite128_4bfd1913f2c26b7d el op0 op1 CRn op2 CRm t t2))
          else
            (do
              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
              then
                (do
                  (TTBR1_EL1_SysRegWrite128_d20c29029eb4ed94 el op0 op1 CRn op2 CRm t t2))
              else
                (do
                  if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                  then
                    (do
                      (TTBR0_EL2_SysRegWrite128_db720477dd35bd78 el op0 op1 CRn op2 CRm t t2))
                  else
                    (do
                      if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                      then
                        (do
                          (TTBR0_EL1_SysRegWrite128_66ee61de597f133e el op0 op1 CRn op2 CRm t t2))
                      else
                        (do
                          if ((((((CRm == 0b0001#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                          then
                            (do
                              (VTTBR_EL2_SysRegWrite128_3ec09d9d33270957 el op0 op1 CRn op2 CRm t t2))
                          else
                            (do
                              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                              then
                                (do
                                  (TTBR0_EL1_SysRegWrite128_8ea27f288a4b152e el op0 op1 CRn op2 CRm
                                    t t2))
                              else
                                (do
                                  if ((((((match CRm with
                                             | b__0 => true : Bool) && (let b__1 := CRn
                                             (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                      b__1 3 3)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                      b__1 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                                             then true
                                             else false : Bool))) && (op0 == 0b11#2)) && (match op1 with
                                         | b__2 => true : Bool)) && (match op2 with
                                       | b__3 => true : Bool)) : Bool)
                                  then
                                    (do
                                      (S3_op1_Cn_Cm_op2_SysRegWrite128_54572e14feed5fe8 el op0 op1
                                        CRn op2 CRm t t2))
                                  else
                                    (do
                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                      then
                                        (do
                                          (RCWMASK_EL1_SysRegWrite128_b8a59eaf95f35a5f el op0 op1
                                            CRn op2 CRm t t2))
                                      else
                                        (do
                                          if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                          then
                                            (do
                                              (TTBR1_EL2_SysRegWrite128_c87556637100112b el op0 op1
                                                CRn op2 CRm t t2))
                                          else
                                            (do
                                              (AArch64_UnallocatedSysRegAccess op0 op1 CRn op2 CRm
                                                false t))))))))))))


/-- Type quantifiers: cp_num : Int -/
def AArch32_SysRegRead (cp_num : Int) (instr : (BitVec 32)) (address : (BitVec 32)) : SailM Unit := do
  let CRd : (BitVec 4) := (Sail.BitVec.extractLsb instr 15 12)
  if (((CRd == 0b0101#4) && ((cp_num == (BitVec.toNat 0xE#4)) : Bool)) : Bool)
  then
    (do
      (AArch32_STC (integer_subrange cp_num 3 0) CRd address))
  else (pure (()))


/-- Type quantifiers: cp_num : Int -/
def AArch32_SysRegWriteM (cp_num : Int) (instr : (BitVec 32)) (address : (BitVec 32)) : SailM Unit := do
  let CRd : (BitVec 4) := (Sail.BitVec.extractLsb instr 15 12)
  if (((CRd == 0b0101#4) && ((cp_num == (BitVec.toNat 0xE#4)) : Bool)) : Bool)
  then
    (do
      (AArch32_LDC (integer_subrange cp_num 3 0) CRd address))
  else (pure (()))


def decode_b_uncond_aarch64_instrs_branch_unconditional_immediate (imm26 : (BitVec 26)) (op : (BitVec 1)) : SailM Unit := do
  let branch_type : BranchType :=
    if ((op == 1#1) : Bool)
    then BranchType_DIRCALL
    else BranchType_DIR
  let offset : (BitVec 64) := (sign_extend (imm26 +++ 0b00#2) 64)
  (execute_aarch64_instrs_branch_unconditional_immediate branch_type offset)


def decode_bl_aarch64_instrs_branch_unconditional_immediate (imm26 : (BitVec 26)) (op : (BitVec 1)) : SailM Unit := do
  let branch_type : BranchType :=
    if ((op == 1#1) : Bool)
    then BranchType_DIRCALL
    else BranchType_DIR
  let offset : (BitVec 64) := (sign_extend (imm26 +++ 0b00#2) 64)
  (execute_aarch64_instrs_branch_unconditional_immediate branch_type offset)


def decode_blr_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
  let n : Nat := (BitVec.toNat Rn)
  let branch_type ← (( do (undefined_BranchType (← occLabel 4005) ()) ) : SailM BranchType )
  let m : Int := (BitVec.toNat Rm)
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let source_is_sp : Bool := ((Z == 1#1) && (m == 31))
  if (((! pac) && (m != 0)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do
        if (pac : Bool)
        then
          (do
            let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
            (pure (((! w__0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (())))
  let branch_type ← (( do
    match op with
    | 0b00 => (pure (BranchType_INDIR))
    | 0b01 => (pure (BranchType_INDCALL))
    | 0b10 => (pure (BranchType_RET))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM BranchType )
  let branch_type := branch_type
  let (n, source_is_sp) ← (( do
    if (pac : Bool)
    then
      (do
        if (((Z == 0#1) && (m != 31)) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        if ((BEq.beq branch_type BranchType_RET) : Bool)
        then
          (do
            if ((n != 31) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let n : Nat := 30
            let source_is_sp : Bool := true
            (pure ((n, source_is_sp))))
        else (pure ((n, source_is_sp))))
    else (pure ((n, source_is_sp))) ) : SailM (Nat × Bool) )
  let n : Int := n
  (execute_aarch64_instrs_branch_unconditional_register branch_type (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pac source_is_sp use_key_a)


def decode_blra_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
  let n : Nat := (BitVec.toNat Rn)
  let branch_type ← (( do (undefined_BranchType (← occLabel 4006) ()) ) : SailM BranchType )
  let m : Int := (BitVec.toNat Rm)
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let source_is_sp : Bool := ((Z == 1#1) && (m == 31))
  if (((! pac) && (m != 0)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do
        if (pac : Bool)
        then
          (do
            let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
            (pure (((! w__0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (())))
  let branch_type ← (( do
    match op with
    | 0b00 => (pure (BranchType_INDIR))
    | 0b01 => (pure (BranchType_INDCALL))
    | 0b10 => (pure (BranchType_RET))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM BranchType )
  let branch_type := branch_type
  let (n, source_is_sp) ← (( do
    if (pac : Bool)
    then
      (do
        if (((Z == 0#1) && (m != 31)) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        if ((BEq.beq branch_type BranchType_RET) : Bool)
        then
          (do
            if ((n != 31) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let n : Nat := 30
            let source_is_sp : Bool := true
            (pure ((n, source_is_sp))))
        else (pure ((n, source_is_sp))))
    else (pure ((n, source_is_sp))) ) : SailM (Nat × Bool) )
  let n : Int := n
  (execute_aarch64_instrs_branch_unconditional_register branch_type (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pac source_is_sp use_key_a)


end ArmFull.Functions
