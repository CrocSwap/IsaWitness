import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0044
import ArmFull.Fn.M0063
import ArmFull.Fn.M0086
import ArmFull.Fn.M0118
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0154
import ArmFull.Fn.M0167
import ArmFull.Fn.M0175
import ArmFull.Fn.M0181
import ArmFull.Fn.M0184
import ArmFull.Fn.M0186
import ArmFull.Fn.M0221
import ArmFull.Fn.M0250
import ArmFull.Fn.M0253
import ArmFull.Fn.M0580
import ArmFull.Fn.M0581
import ArmFull.Fn.M0583
import ArmFull.Fn.M0713
import ArmFull.Fn.M0714
import ArmFull.Fn.M0715
import ArmFull.Fn.M0716
import ArmFull.Fn.M0717
import ArmFull.Fn.M0718
import ArmFull.Fn.M0719
import ArmFull.Fn.M0720
import ArmFull.Fn.M0721
import ArmFull.Fn.M0722
import ArmFull.Fn.M0723
import ArmFull.Fn.M0724
import ArmFull.Fn.M0725
import ArmFull.Fn.M0726
import ArmFull.Fn.M0727
import ArmFull.Fn.M0836
import ArmFull.Fn.M0839

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

/-- Type quantifiers: t : Int, t2 : Int -/
def AArch32_AutoGen_SysRegRead64 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  if ((((CRm == 0b0010#4) && (coproc == 0b1110#4)) && (opc1 == 0b0000#4)) : Bool)
  then
    (do
      (DBGDSAR_SysRegRead64_2f971e6eb001648b el coproc opc1 CRm t t2))
  else
    (do
      if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
      then
        (do
          (CNTVOFF_SysRegRead64_66c4d48806fce48e el coproc opc1 CRm t t2))
      else
        (do
          if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
          then
            (do
              (CNTHV_CVAL_SysRegRead64_7bf312f271feb72e el coproc opc1 CRm t t2))
          else
            (do
              if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
              then
                (do
                  (CNTHPS_CVAL_SysRegRead64_aa5fa6170d1a3db5 el coproc opc1 CRm t t2))
              else
                (do
                  if ((((CRm == 0b0111#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                  then
                    (do
                      (PAR_SysRegRead64_bd143a1fe560ae4b el coproc opc1 CRm t t2))
                  else
                    (do
                      if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                      then
                        (do
                          (CNTPCT_SysRegRead64_7dc4fea5bbad7fe9 el coproc opc1 CRm t t2))
                      else
                        (do
                          if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                          then
                            (do
                              (CNTHP_CVAL_SysRegRead64_bedb5ea1dc82962f el coproc opc1 CRm t t2))
                          else
                            (do
                              if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b1000#4)) : Bool)
                              then
                                (do
                                  (CNTPCT_SysRegRead64_7dc4fea5bbad7fe9 el coproc opc1 CRm t t2))
                              else
                                (do
                                  if ((((CRm == 0b1001#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                  then
                                    (do
                                      (PMCCNTR_SysRegRead64_1cf48d19bc879bd3 el coproc opc1 CRm t t2))
                                  else
                                    (do
                                      if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                      then
                                        (do
                                          (CNTVCT_SysRegRead64_6e373436952b9ca9 el coproc opc1 CRm t
                                            t2))
                                      else
                                        (do
                                          if ((((CRm == 0b1110#4) && (coproc == 0b1111#4)) && (opc1 == 0b1001#4)) : Bool)
                                          then
                                            (do
                                              (CNTVCT_SysRegRead64_6e373436952b9ca9 el coproc opc1
                                                CRm t t2))
                                          else
                                            (do
                                              if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                              then
                                                (do
                                                  (TTBR1_SysRegRead64_6988488afc2dce1a el coproc
                                                    opc1 CRm t t2))
                                              else
                                                (do
                                                  if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
                                                  then
                                                    (do
                                                      (HTTBR_SysRegRead64_5b679aebf4474d8a el coproc
                                                        opc1 CRm t t2))
                                                  else
                                                    (do
                                                      if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                      then
                                                        (do
                                                          (TTBR0_SysRegRead64_9396816aa24cfa90 el
                                                            coproc opc1 CRm t t2))
                                                      else
                                                        (do
                                                          if ((((CRm == 0b0001#4) && (coproc == 0b1110#4)) && (opc1 == 0b0000#4)) : Bool)
                                                          then
                                                            (do
                                                              (DBGDRAR_SysRegRead64_89f87ddb7d53b509
                                                                el coproc opc1 CRm t t2))
                                                          else
                                                            (do
                                                              if ((((CRm == 0b0010#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                                                              then
                                                                (do
                                                                  (VTTBR_SysRegRead64_aec948eb11ac7d09
                                                                    el coproc opc1 CRm t t2))
                                                              else
                                                                (do
                                                                  if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                                                                  then
                                                                    (do
                                                                      (AMEVCNTR0_SysRegRead64_58cd2445e81e8975
                                                                        el coproc opc1 CRm t t2))
                                                                  else
                                                                    (do
                                                                      if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                                                                      then
                                                                        (do
                                                                          (AMEVCNTR0_SysRegRead64_bf8f308b8b559115
                                                                            el coproc opc1 CRm t t2))
                                                                      else
                                                                        (do
                                                                          if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                                                          then
                                                                            (do
                                                                              (AMEVCNTR0_SysRegRead64_66e81afe82d2c192
                                                                                el coproc opc1 CRm t
                                                                                t2))
                                                                          else
                                                                            (do
                                                                              if ((((CRm == 0b0000#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                                              then
                                                                                (do
                                                                                  (AMEVCNTR0_SysRegRead64_2b274c768298c3f9
                                                                                    el coproc opc1
                                                                                    CRm t t2))
                                                                              else
                                                                                (do
                                                                                  if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0111#4)) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      (AMEVCNTR1_SysRegRead64_51a9ce69caa26d97
                                                                                        el coproc
                                                                                        opc1 CRm t
                                                                                        t2))
                                                                                  else
                                                                                    (do
                                                                                      if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          (AMEVCNTR1_SysRegRead64_cdf416f7d354cbf5
                                                                                            el
                                                                                            coproc
                                                                                            opc1 CRm
                                                                                            t t2))
                                                                                      else
                                                                                        (do
                                                                                          if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0101#4)) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              (AMEVCNTR1_SysRegRead64_065fe37bc5a680bd
                                                                                                el
                                                                                                coproc
                                                                                                opc1
                                                                                                CRm
                                                                                                t t2))
                                                                                          else
                                                                                            (do
                                                                                              if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  (AMEVCNTR1_SysRegRead64_d4ffe491a2456c2b
                                                                                                    el
                                                                                                    coproc
                                                                                                    opc1
                                                                                                    CRm
                                                                                                    t
                                                                                                    t2))
                                                                                              else
                                                                                                (do
                                                                                                  if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      (AMEVCNTR1_SysRegRead64_839ed88b8f796549
                                                                                                        el
                                                                                                        coproc
                                                                                                        opc1
                                                                                                        CRm
                                                                                                        t
                                                                                                        t2))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          (AMEVCNTR1_SysRegRead64_fa3226080978524b
                                                                                                            el
                                                                                                            coproc
                                                                                                            opc1
                                                                                                            CRm
                                                                                                            t
                                                                                                            t2))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              (AMEVCNTR1_SysRegRead64_4cd25036d674f8ac
                                                                                                                el
                                                                                                                coproc
                                                                                                                opc1
                                                                                                                CRm
                                                                                                                t
                                                                                                                t2))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((((CRm == 0b0101#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  (AMEVCNTR1_SysRegRead64_9c104b95f67d3b22
                                                                                                                    el
                                                                                                                    coproc
                                                                                                                    opc1
                                                                                                                    CRm
                                                                                                                    t
                                                                                                                    t2))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0111#4)) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      (AMEVCNTR1_SysRegRead64_141e5d18f9a75c13
                                                                                                                        el
                                                                                                                        coproc
                                                                                                                        opc1
                                                                                                                        CRm
                                                                                                                        t
                                                                                                                        t2))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0110#4)) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          (AMEVCNTR1_SysRegRead64_6f64074808614759
                                                                                                                            el
                                                                                                                            coproc
                                                                                                                            opc1
                                                                                                                            CRm
                                                                                                                            t
                                                                                                                            t2))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0101#4)) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              (AMEVCNTR1_SysRegRead64_2d5e01434567b282
                                                                                                                                el
                                                                                                                                coproc
                                                                                                                                opc1
                                                                                                                                CRm
                                                                                                                                t
                                                                                                                                t2))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0100#4)) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  (AMEVCNTR1_SysRegRead64_eefece484f7466c9
                                                                                                                                    el
                                                                                                                                    coproc
                                                                                                                                    opc1
                                                                                                                                    CRm
                                                                                                                                    t
                                                                                                                                    t2))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0011#4)) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      (AMEVCNTR1_SysRegRead64_4e22e3365cdbab7d
                                                                                                                                        el
                                                                                                                                        coproc
                                                                                                                                        opc1
                                                                                                                                        CRm
                                                                                                                                        t
                                                                                                                                        t2))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0010#4)) : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          (AMEVCNTR1_SysRegRead64_13f84beb778d3114
                                                                                                                                            el
                                                                                                                                            coproc
                                                                                                                                            opc1
                                                                                                                                            CRm
                                                                                                                                            t
                                                                                                                                            t2))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0001#4)) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              (AMEVCNTR1_SysRegRead64_132f33bfb64bea99
                                                                                                                                                el
                                                                                                                                                coproc
                                                                                                                                                opc1
                                                                                                                                                CRm
                                                                                                                                                t
                                                                                                                                                t2))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((((CRm == 0b0100#4) && (coproc == 0b1111#4)) && (opc1 == 0b0000#4)) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  (AMEVCNTR1_SysRegRead64_a118420696d1228f
                                                                                                                                                    el
                                                                                                                                                    coproc
                                                                                                                                                    opc1
                                                                                                                                                    CRm
                                                                                                                                                    t
                                                                                                                                                    t2))
                                                                                                                                              else
                                                                                                                                                sailThrow ((Error_Undefined
                                                                                                                                                  ())))))))))))))))))))))))))))))))))))))


/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int, t2 : Int -/
def AArch64_SysInstr128 (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (AArch64_AutoGen_SysOpsWrite128 w__0.EL (integer_subrange op0 1 0) (integer_subrange op1 2 0)
    (integer_subrange crn 3 0) (integer_subrange op2 2 0) (integer_subrange crm 3 0) t t2)


def decode_aarch32_instrs_SVC_A1enc_A_txt (cond : (BitVec 4)) (imm24 : (BitVec 24)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:16058.29-16058.30"
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm24 32)
      (execute_aarch32_instrs_SVC_Op_A_txt imm32))
  else (pure (()))


def decode_aarch32_instrs_SVC_T1enc_A_txt (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      (execute_aarch32_instrs_SVC_Op_A_txt imm32))
  else (pure (()))


def execute_aarch32_instrs_WFE_Op_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (IsEventRegisterSet ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (ClearEventRegister ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__1.EL == EL0) : Bool)
      then
        (do
          (AArch32_CheckForWFxTrap EL1 WFxType_WFE))
      else (pure (()))
      let w__8 ← (( do
        if ((← do
             if ((← do
                  if ((← do
                       let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__2.EL == EL0) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__3.EL == EL1) : Bool))))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__7 ← (( do (IsInHost ()) ) : SailM Bool )
            (pure (((! w__7) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch32_CheckForWFxTrap EL2 WFxType_WFE))
      else (pure (()))
      let w__10 ← (( do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__9.M != M32_Monitor) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__10 : Bool)
      then
        (do
          (AArch32_CheckForWFxTrap EL3 WFxType_WFE))
      else (pure (()))
      let localtimeout : Int := (Int.shiftl 1 64)
      (WaitForEvent localtimeout))


def execute_aarch32_instrs_WFI_Op_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (InterruptPending ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__1.EL == EL0) : Bool)
      then
        (do
          (AArch32_CheckForWFxTrap EL1 WFxType_WFI))
      else (pure (()))
      let w__8 ← (( do
        if ((← do
             if ((← do
                  if ((← do
                       let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__2.EL == EL0) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__3.EL == EL1) : Bool))))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__7 ← (( do (IsInHost ()) ) : SailM Bool )
            (pure (((! w__7) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch32_CheckForWFxTrap EL2 WFxType_WFI))
      else (pure (()))
      let w__10 ← (( do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__9.M != M32_Monitor) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__10 : Bool)
      then
        (do
          (AArch32_CheckForWFxTrap EL3 WFxType_WFI))
      else (pure (()))
      let localtimeout : Int := (Int.shiftl 1 64)
      (WaitForInterrupt localtimeout))
  else (pure (()))


def decode_aarch32_instrs_HVC_A1enc_A_txt (cond : (BitVec 4)) (imm12 : (BitVec 12)) (imm4 : (BitVec 4)) : SailM Unit := do
  ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:40919.25-40919.26"
  if ((cond != 0b1110#4) : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let imm16 : (BitVec 16) := (imm12 +++ imm4)
  (execute_aarch32_instrs_HVC_Op_AS_txt imm16)


def decode_aarch32_instrs_HVC_T1enc_A_txt (imm4 : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let imm16 : (BitVec 16) := (imm4 +++ imm12)
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  (execute_aarch32_instrs_HVC_Op_AS_txt imm16)


def decode_aarch32_instrs_SMC_A1enc_AS_txt (cond : (BitVec 4)) (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:41716.29-41716.30"
      (execute_aarch32_instrs_SMC_Op_AS_txt ()))
  else (pure (()))


def decode_aarch32_instrs_SMC_T1enc_AS_txt (imm4 : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SMC_Op_AS_txt ()))
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_autda_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let auth_then_branch : Bool := false
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then
        (do
          let w__1 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__2 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (AuthDA w__1 w__2 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__3))
      else
        (do
          let w__4 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__5 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
          let w__6 ← (( do (AuthDA w__4 w__5 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__6)))
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_autdb_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let auth_then_branch : Bool := false
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then
        (do
          let w__1 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__2 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (AuthDB w__1 w__2 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__3))
      else
        (do
          let w__4 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__5 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
          let w__6 ← (( do (AuthDB w__4 w__5 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__6)))
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_autia_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let auth_then_branch : Bool := false
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then
        (do
          let w__1 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__2 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (AuthIA w__1 w__2 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__3))
      else
        (do
          let w__4 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__5 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
          let w__6 ← (( do (AuthIA w__4 w__5 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__6)))
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_autib_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let auth_then_branch : Bool := false
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then
        (do
          let w__1 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__2 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (AuthIB w__1 w__2 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__3))
      else
        (do
          let w__4 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__5 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
          let w__6 ← (( do (AuthIB w__4 w__5 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__6)))
  else (pure (()))


/-- Type quantifiers: k_pac : Bool, k_use_key_a : Bool -/
def execute_aarch64_instrs_branch_unconditional_eret (pac : Bool) (use_key_a : Bool) : SailM Unit := do
  (AArch64_CheckForERetTrap pac use_key_a)
  let target ← (( do (ELR_read__1 ()) ) : SailM (BitVec 64) )
  let modifier ← (( do (SP_read ()) ) : SailM (BitVec 64) )
  let auth_then_branch : Bool := true
  let target ← (( do
    if (pac : Bool)
    then
      (do
        if (use_key_a : Bool)
        then
          (do
            (AuthIA target modifier auth_then_branch))
        else
          (do
            (AuthIB target modifier auth_then_branch)))
    else (pure (target)) ) : SailM (BitVec 64) )
  (return_exception (Sail.BitVec.extractLsb target 55 0))
  let w__2 ← (( do (SPSR_read (N := 64)) ) : SailM (BitVec 64) )
  (AArch64_ExceptionReturn target w__2)


end ArmFull.Functions
