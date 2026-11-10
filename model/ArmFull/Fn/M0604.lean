import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0036
import ArmFull.Fn.M0042
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0057
import ArmFull.Fn.M0059
import ArmFull.Fn.M0081
import ArmFull.Fn.M0082
import ArmFull.Fn.M0092
import ArmFull.Fn.M0139
import ArmFull.Fn.M0141
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0198
import ArmFull.Fn.M0203
import ArmFull.Fn.M0254
import ArmFull.Fn.M0260

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
def CCSIDR2_SysRegRead32_b747ebd0fcc6df4e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID2 : (BitVec 1) := (_get_HCR_EL2_Type_TID2 w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID4 : (BitVec 1) := (_get_HCR_EL2_Type_TID4 w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TID2 : (BitVec 1) := (_get_HCR_Type_TID2 w__5)
  let w__6 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  let __HCR2_TID4 : (BitVec 1) := (_get_HCR2_Type_TID4 w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__8 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__8) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__14 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T0 == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__16 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__16) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TID2 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__22 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__20 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__20) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TID4 == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__26 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TID2 == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__26 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCR2_TID4 == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__30 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__31 ← (( do (CCSIDR2_read ()) ) : SailM (BitVec 32) )
                                  (R_set t (__get_CCSIDR2 w__31)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__32 ← (( do (CCSIDR2_read ()) ) : SailM (BitVec 32) )
              (R_set t (__get_CCSIDR2 w__32)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__33 ← (( do (CCSIDR2_read ()) ) : SailM (BitVec 32) )
                  (R_set t (__get_CCSIDR2 w__33)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CCSIDR_SysRegRead32_4e417948cc9050d5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID2 : (BitVec 1) := (_get_HCR_EL2_Type_TID2 w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID4 : (BitVec 1) := (_get_HCR_EL2_Type_TID4 w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TID2 : (BitVec 1) := (_get_HCR_Type_TID2 w__5)
  let w__6 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  let __HCR2_TID4 : (BitVec 1) := (_get_HCR2_Type_TID4 w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__8 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__8) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__14 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T0 == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__16 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__16) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TID2 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__22 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__20 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__20) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TID4 == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__26 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TID2 == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__26 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCR2_TID4 == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__30 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__31 ← (( do (CCSIDR_read ()) ) : SailM (BitVec 32) )
                                  (R_set t w__31))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__32 ← (( do (CCSIDR_read ()) ) : SailM (BitVec 32) )
              (R_set t w__32))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__33 ← (( do (CCSIDR_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__33))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CLIDR_SysRegRead32_1324f310591d527a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID2 : (BitVec 1) := (_get_HCR_EL2_Type_TID2 w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID4 : (BitVec 1) := (_get_HCR_EL2_Type_TID4 w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TID2 : (BitVec 1) := (_get_HCR_Type_TID2 w__5)
  let w__6 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  let __HCR2_TID4 : (BitVec 1) := (_get_HCR2_Type_TID4 w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__8 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__8) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__14 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T0 == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__16 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__16) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TID2 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__22 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__20 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__20) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TID4 == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__26 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TID2 == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__26 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCR2_TID4 == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__30 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__31 ← (( do (CLIDR_read ()) ) : SailM (BitVec 32) )
                                  (R_set t w__31))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__32 ← (( do (CLIDR_read ()) ) : SailM (BitVec 32) )
              (R_set t w__32))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__33 ← (( do (CLIDR_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__33))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTFRQ_SysRegRead32_4d7a0faa14f3d1f9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
  let __CNTKCTL_PL0PCTEN : (BitVec 1) := (_get_CNTKCTL_Type_PL0PCTEN w__2)
  let w__3 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
  let __CNTKCTL_PL0VCTEN : (BitVec 1) := (_get_CNTKCTL_Type_PL0VCTEN w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__13 ← (( do
        if ((← do
             if ((← do
                  let w__5 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                  (pure (((! w__5) : Bool)))) : Bool)
             then
               (do
                 let w__9 ← (( do
                   if ((← do
                        (EL2Enabled ())) : Bool)
                   then
                     (do
                       let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       (pure (((((_get_HCR_EL2_Type_E2H w__7) +++ (_get_HCR_EL2_Type_TGE w__8)) == 0b11#2) : Bool))))
                   else (pure false) ) : SailM Bool )
                 (pure (((! w__9) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__11 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
            let w__12 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
            (pure (((((_get_CNTKCTL_EL1_Type_EL0PCTEN w__11) +++ (_get_CNTKCTL_EL1_Type_EL0VCTEN
                    w__12)) == 0b00#2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__13 : Bool)
      then
        (do
          let w__17 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__15) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__17 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
      else
        (do
          let w__20 ← (( do
            (pure ((← do
                  (pure ((← do
                        (ELUsingAArch32 EL1)) && ((__CNTKCTL_PL0PCTEN == 0#1) : Bool)))) && ((__CNTKCTL_PL0VCTEN == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__20 : Bool)
          then
            (do
              let w__24 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__22 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__22) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__24 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__28 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__28 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              let w__37 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__30 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__30) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         (pure (((((_get_HCR_EL2_Type_E2H w__32) +++ (_get_HCR_EL2_Type_TGE w__33)) == 0b11#2) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__35 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                    let w__36 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_CNTHCTL_EL2_Type_EL0PCTEN w__35) +++ (_get_CNTHCTL_EL2_Type_EL0VCTEN
                            w__36)) == 0b00#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__37 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__38 ← (( do (CNTFRQ_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__38)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__39 ← (( do (CNTFRQ_read ()) ) : SailM (BitVec 32) )
          (R_set t w__39))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__40 ← (( do (CNTFRQ_read ()) ) : SailM (BitVec 32) )
              (R_set t w__40))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__41 ← (( do (CNTFRQ_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__41))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHPS_CTL_SysRegRead32_a99d410e49082e9f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0PTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0PTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
  let __CNTKCTL_PL0PTEN : (BitVec 1) := (_get_CNTKCTL_Type_PL0PTEN w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__5)
  let w__6 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1PCEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1PCEN w__6)
  let w__7 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1PTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1PTEN w__7)
  let w__8 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0PTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0PTEN w__8)
  let w__9 ← (( do (CNTHCTL_read ()) ) : SailM (BitVec 32) )
  let __CNTHCTL_PL1PCEN : (BitVec 1) := (_get_CNTHCTL_Type_PL1PCEN w__9)
  let w__10 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__10)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__17 ← (( do
        (pure ((← do
              if ((← do
                   let w__11 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__11) : Bool)))) : Bool)
              then
                (do
                  let w__15 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__13) +++ (_get_HCR_EL2_Type_TGE w__14)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__15) : Bool))))
              else (pure false)) && ((__CNTKCTL_EL1_EL0PTEN == 0#1) : Bool))) ) : SailM Bool )
      if (w__17 : Bool)
      then
        (do
          let w__21 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__19 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__19) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__21 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
      else
        (do
          let w__23 ← (( do
            (pure ((← do
                  (ELUsingAArch32 EL1)) && ((__CNTKCTL_PL0PTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
          then
            (do
              let w__27 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__25 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__25) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__27 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              let w__36 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__33 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__33) : Bool))))
                            else (pure false)) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__36 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__43 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__38 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__38) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__40) +++ (_get_HCR_EL2_Type_TGE
                                      w__41)) == 0b10#2) : Bool))))
                          else (pure false)) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__43 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__50 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       let w__45 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                       (pure (((! w__45) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__47 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__47) +++ (_get_HCR_EL2_Type_TGE
                                          w__48)) == 0b11#2) : Bool))))
                              else (pure false)) && ((__CNTHCTL_EL2_EL0PTEN == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__50 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__CNTHCTL_PL1PCEN == 0#1) : Bool))) ) :
                            SailM Bool )
                          if (w__54 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__64 ← (( do
                                if ((← do
                                     if ((← do
                                          if ((← do
                                               if ((← do
                                                    (EL2Enabled ())) : Bool)
                                               then
                                                 (do
                                                   let w__56 ← (( do (ELUsingAArch32 EL2) ) :
                                                     SailM Bool )
                                                   (pure (((! w__56) : Bool))))
                                               else (pure false)) : Bool)
                                          then
                                            (do
                                              let w__58 ← (( do readReg HCR_EL2 ) : SailM
                                                (BitVec 64) )
                                              let w__59 ← (( do readReg HCR_EL2 ) : SailM
                                                (BitVec 64) )
                                              (pure (((((_get_HCR_EL2_Type_E2H w__58) +++ (_get_HCR_EL2_Type_TGE
                                                      w__59)) == 0b11#2) : Bool))))
                                          else (pure false)) : Bool)
                                     then
                                       (do
                                         let w__61 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                         (pure ((((_get_SCR_EL3_Type_NS w__61) == 0#1) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_SEL2))
                                else (pure false) ) : SailM Bool )
                              if (w__64 : Bool)
                              then
                                (do
                                  let w__65 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
                                  (R_set t
                                    (Sail.BitVec.extractLsb (__get_CNTHPS_CTL_EL2 w__65) 31 0)))
                              else
                                (do
                                  let w__73 ← (( do
                                    if ((← do
                                         if ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__67 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__67) : Bool))))
                                              else (pure false)) : Bool)
                                         then
                                           (do
                                             let w__69 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             let w__70 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             (pure (((((_get_HCR_EL2_Type_E2H w__69) +++ (_get_HCR_EL2_Type_TGE
                                                     w__70)) == 0b11#2) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__72 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                        (pure ((((_get_SCR_EL3_Type_NS w__72) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__73 : Bool)
                                  then
                                    (do
                                      let w__74 ← (( do readReg CNTHP_CTL_EL2 ) : SailM
                                        (BitVec 64) )
                                      (R_set t
                                        (Sail.BitVec.extractLsb (__get_CNTHP_CTL_EL2 w__74) 31 0)))
                                  else
                                    (do
                                      let w__75 ← (( do (CNTP_CTL_read ()) ) : SailM (BitVec 32) )
                                      (R_set t (__get_CNTP_CTL w__75)))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__80 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__77 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                            (pure (((! w__77) : Bool))))
                        else (pure false)) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__80 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__85 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__82 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__82) : Bool))))
                            else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__85 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__89 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__CNTHCTL_PL1PCEN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__89 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__91 ← (( do
                        if (((HaveEL EL3) : Bool) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL3))
                        else (pure false) ) : SailM Bool )
                      if (w__91 : Bool)
                      then
                        (do
                          let w__92 ← (( do (CNTP_CTL_NS_read ()) ) : SailM (BitVec 32) )
                          (R_set t (__get_CNTP_CTL_NS w__92)))
                      else
                        (do
                          let w__93 ← (( do (CNTP_CTL_read ()) ) : SailM (BitVec 32) )
                          (R_set t (__get_CNTP_CTL w__93)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__95 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__95 : Bool)
              then
                (do
                  let w__96 ← (( do (CNTP_CTL_NS_read ()) ) : SailM (BitVec 32) )
                  (R_set t (__get_CNTP_CTL_NS w__96)))
              else
                (do
                  let w__97 ← (( do (CNTP_CTL_read ()) ) : SailM (BitVec 32) )
                  (R_set t (__get_CNTP_CTL w__97))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__98 ← (( do readReg CNTP_CTL_S ) : SailM (BitVec 32) )
                      (R_set t (__get_CNTP_CTL_S w__98)))
                  else
                    (do
                      let w__99 ← (( do (CNTP_CTL_NS_read ()) ) : SailM (BitVec 32) )
                      (R_set t (__get_CNTP_CTL_NS w__99))))
              else (pure (())))))


end ArmFull.Functions
