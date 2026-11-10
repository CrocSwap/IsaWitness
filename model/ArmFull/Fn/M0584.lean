import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0054
import ArmFull.Fn.M0058
import ArmFull.Fn.M0059
import ArmFull.Fn.M0080
import ArmFull.Fn.M0144
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0202
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

/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegWrite64_125e5d1a241e0a34 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__1)
  let w__8 ← (( do
    (pure ((← do
          (pure ((← do
                if ((← do
                     if ((← do
                          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__2.EL == EL1) : Bool)))) : Bool)
                     then
                       (do
                         (EL2Enabled ()))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                    (pure (((! w__5) : Bool))))
                else (pure false)) && ((3 <b 8) : Bool)))) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) :
    SailM Bool )
  if (w__8 : Bool)
  then
    (do
      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
  else
    (do
      let w__15 ← (( do
        (pure ((← do
              (pure ((← do
                    if ((← do
                         if ((← do
                              let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                         then
                           (do
                             (EL2Enabled ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL2))
                    else (pure false)) && ((3 <b 8) : Bool)))) && ((__HSTR_T0 == 1#1) : Bool))) ) :
        SailM Bool )
      if (w__15 : Bool)
      then
        (do
          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
      else
        (do
          let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((IsHighestEL w__16.EL) : Bool)
          then
            (do
              let w__17 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
              let w__18 ← (( do (R_read t2) ) : SailM (BitVec 32) )
              let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
              writeReg AMEVCNTR0 (vectorUpdate w__17 3 (Mk_AMEVCNTR0_Type (w__18 +++ w__19))))
          else sailThrow ((Error_Undefined ()))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegWrite64_a509b10e64184e5e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__1)
  let w__8 ← (( do
    (pure ((← do
          (pure ((← do
                if ((← do
                     if ((← do
                          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__2.EL == EL1) : Bool)))) : Bool)
                     then
                       (do
                         (EL2Enabled ()))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                    (pure (((! w__5) : Bool))))
                else (pure false)) && ((2 <b 8) : Bool)))) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) :
    SailM Bool )
  if (w__8 : Bool)
  then
    (do
      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
  else
    (do
      let w__15 ← (( do
        (pure ((← do
              (pure ((← do
                    if ((← do
                         if ((← do
                              let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                         then
                           (do
                             (EL2Enabled ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL2))
                    else (pure false)) && ((2 <b 8) : Bool)))) && ((__HSTR_T0 == 1#1) : Bool))) ) :
        SailM Bool )
      if (w__15 : Bool)
      then
        (do
          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
      else
        (do
          let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((IsHighestEL w__16.EL) : Bool)
          then
            (do
              let w__17 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
              let w__18 ← (( do (R_read t2) ) : SailM (BitVec 32) )
              let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
              writeReg AMEVCNTR0 (vectorUpdate w__17 2 (Mk_AMEVCNTR0_Type (w__18 +++ w__19))))
          else sailThrow ((Error_Undefined ()))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegWrite64_ffac5e218d5b074d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__1)
  let w__8 ← (( do
    (pure ((← do
          (pure ((← do
                if ((← do
                     if ((← do
                          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__2.EL == EL1) : Bool)))) : Bool)
                     then
                       (do
                         (EL2Enabled ()))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                    (pure (((! w__5) : Bool))))
                else (pure false)) && ((1 <b 8) : Bool)))) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) :
    SailM Bool )
  if (w__8 : Bool)
  then
    (do
      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
  else
    (do
      let w__15 ← (( do
        (pure ((← do
              (pure ((← do
                    if ((← do
                         if ((← do
                              let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                         then
                           (do
                             (EL2Enabled ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL2))
                    else (pure false)) && ((1 <b 8) : Bool)))) && ((__HSTR_T0 == 1#1) : Bool))) ) :
        SailM Bool )
      if (w__15 : Bool)
      then
        (do
          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
      else
        (do
          let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((IsHighestEL w__16.EL) : Bool)
          then
            (do
              let w__17 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
              let w__18 ← (( do (R_read t2) ) : SailM (BitVec 32) )
              let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
              writeReg AMEVCNTR0 (vectorUpdate w__17 1 (Mk_AMEVCNTR0_Type (w__18 +++ w__19))))
          else sailThrow ((Error_Undefined ()))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_1415f513493b61c8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 10) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do
        (pure ((← do
              (pure ((← do
                    if ((← do
                         if ((← do
                              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                         then
                           (do
                             (EL2Enabled ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                        (pure (((! w__6) : Bool))))
                    else (pure false)) && ((10 ≥b 8) : Bool)))) && ((__HSTR_EL2_T5 == 1#1) : Bool)))
        ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             if ((← do
                                  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                                  (pure (((w__10.EL == EL1) : Bool)))) : Bool)
                             then
                               (do
                                 (EL2Enabled ()))
                             else (pure false)) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL2))
                        else (pure false)) && ((10 ≥b 8) : Bool)))) && ((__HSTR_T5 == 1#1) : Bool)))
            ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
          else
            (do
              let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((IsHighestEL w__17.EL) : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVCNTR1_set 10 (Mk_AMEVCNTR1_Type (w__18 +++ w__19))))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_3cf44094d12f6f9a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 12) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do
        (pure ((← do
              (pure ((← do
                    if ((← do
                         if ((← do
                              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                         then
                           (do
                             (EL2Enabled ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                        (pure (((! w__6) : Bool))))
                    else (pure false)) && ((12 ≥b 8) : Bool)))) && ((__HSTR_EL2_T5 == 1#1) : Bool)))
        ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             if ((← do
                                  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                                  (pure (((w__10.EL == EL1) : Bool)))) : Bool)
                             then
                               (do
                                 (EL2Enabled ()))
                             else (pure false)) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL2))
                        else (pure false)) && ((12 ≥b 8) : Bool)))) && ((__HSTR_T5 == 1#1) : Bool)))
            ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
          else
            (do
              let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((IsHighestEL w__17.EL) : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVCNTR1_set 12 (Mk_AMEVCNTR1_Type (w__18 +++ w__19))))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_469c861805be726d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 15) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do
        (pure ((← do
              (pure ((← do
                    if ((← do
                         if ((← do
                              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                         then
                           (do
                             (EL2Enabled ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                        (pure (((! w__6) : Bool))))
                    else (pure false)) && ((15 ≥b 8) : Bool)))) && ((__HSTR_EL2_T5 == 1#1) : Bool)))
        ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             if ((← do
                                  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                                  (pure (((w__10.EL == EL1) : Bool)))) : Bool)
                             then
                               (do
                                 (EL2Enabled ()))
                             else (pure false)) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL2))
                        else (pure false)) && ((15 ≥b 8) : Bool)))) && ((__HSTR_T5 == 1#1) : Bool)))
            ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
          else
            (do
              let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((IsHighestEL w__17.EL) : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVCNTR1_set 15 (Mk_AMEVCNTR1_Type (w__18 +++ w__19))))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_683d5eccd985c418 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 8) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do
        (pure ((← do
              (pure ((← do
                    if ((← do
                         if ((← do
                              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                         then
                           (do
                             (EL2Enabled ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                        (pure (((! w__6) : Bool))))
                    else (pure false)) && ((8 ≥b 8) : Bool)))) && ((__HSTR_EL2_T5 == 1#1) : Bool)))
        ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             if ((← do
                                  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                                  (pure (((w__10.EL == EL1) : Bool)))) : Bool)
                             then
                               (do
                                 (EL2Enabled ()))
                             else (pure false)) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL2))
                        else (pure false)) && ((8 ≥b 8) : Bool)))) && ((__HSTR_T5 == 1#1) : Bool)))
            ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
          else
            (do
              let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((IsHighestEL w__17.EL) : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVCNTR1_set 8 (Mk_AMEVCNTR1_Type (w__18 +++ w__19))))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_6aa1c0a95da044bc (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 13) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do
        (pure ((← do
              (pure ((← do
                    if ((← do
                         if ((← do
                              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                         then
                           (do
                             (EL2Enabled ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                        (pure (((! w__6) : Bool))))
                    else (pure false)) && ((13 ≥b 8) : Bool)))) && ((__HSTR_EL2_T5 == 1#1) : Bool)))
        ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             if ((← do
                                  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                                  (pure (((w__10.EL == EL1) : Bool)))) : Bool)
                             then
                               (do
                                 (EL2Enabled ()))
                             else (pure false)) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL2))
                        else (pure false)) && ((13 ≥b 8) : Bool)))) && ((__HSTR_T5 == 1#1) : Bool)))
            ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
          else
            (do
              let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((IsHighestEL w__17.EL) : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVCNTR1_set 13 (Mk_AMEVCNTR1_Type (w__18 +++ w__19))))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_8df7cb996ace4301 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 11) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do
        (pure ((← do
              (pure ((← do
                    if ((← do
                         if ((← do
                              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                         then
                           (do
                             (EL2Enabled ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                        (pure (((! w__6) : Bool))))
                    else (pure false)) && ((11 ≥b 8) : Bool)))) && ((__HSTR_EL2_T5 == 1#1) : Bool)))
        ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             if ((← do
                                  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                                  (pure (((w__10.EL == EL1) : Bool)))) : Bool)
                             then
                               (do
                                 (EL2Enabled ()))
                             else (pure false)) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL2))
                        else (pure false)) && ((11 ≥b 8) : Bool)))) && ((__HSTR_T5 == 1#1) : Bool)))
            ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
          else
            (do
              let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((IsHighestEL w__17.EL) : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVCNTR1_set 11 (Mk_AMEVCNTR1_Type (w__18 +++ w__19))))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR1_SysRegWrite64_caa18a28b827223b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 14) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do
        (pure ((← do
              (pure ((← do
                    if ((← do
                         if ((← do
                              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                         then
                           (do
                             (EL2Enabled ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                        (pure (((! w__6) : Bool))))
                    else (pure false)) && ((14 ≥b 8) : Bool)))) && ((__HSTR_EL2_T5 == 1#1) : Bool)))
        ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             if ((← do
                                  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                                  (pure (((w__10.EL == EL1) : Bool)))) : Bool)
                             then
                               (do
                                 (EL2Enabled ()))
                             else (pure false)) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL2))
                        else (pure false)) && ((14 ≥b 8) : Bool)))) && ((__HSTR_T5 == 1#1) : Bool)))
            ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
          else
            (do
              let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((IsHighestEL w__17.EL) : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVCNTR1_set 14 (Mk_AMEVCNTR1_Type (w__18 +++ w__19))))
              else sailThrow ((Error_Undefined ())))))


end ArmFull.Functions
