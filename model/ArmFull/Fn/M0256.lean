import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0145
import ArmFull.Fn.M0168
import ArmFull.Fn.M0172
import ArmFull.Fn.M0181
import ArmFull.Fn.M0195
import ArmFull.Fn.M0241
import ArmFull.Fn.M0252

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

def AddPACIA (x : (BitVec 64)) (y : (BitVec 64)) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool_at (← occLabel 1299) ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool_at (← occLabel 1300) ()) ) : SailM Bool )
  let Enable ← (( do (undefined_bitvector_at (← occLabel 1301) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do readReg APIAKeyHi_EL1 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg APIAKeyLo_EL1 ) : SailM (BitVec 64) )
  let APIAKey_EL1 : (BitVec 128) :=
    ((Sail.BitVec.extractLsb w__0 63 0) +++ (Sail.BitVec.extractLsb w__1 63 0))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__2.EL
  let (Enable, TrapEL2, TrapEL3) ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (do
        let w__3 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
        let IsEL1Regime : Bool := (w__3 == EL1)
        let w__6 ← (( do
          if (IsEL1Regime : Bool)
          then
            (do
              let w__4 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL1_Type_EnIA w__4))))
          else
            (do
              let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL2_Type_EnIA w__5)))) ) : SailM (BitVec 1) )
        let Enable := (w__6 : (BitVec 1))
        let w__13 ← (( do
          if ((← do
               if ((← do
                    (EL2Enabled ())) : Bool)
               then
                 (do
                   let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_API w__8) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_TGE w__10) == 0#1) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_E2H w__11) == 0#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let TrapEL2 := (w__13 : Bool)
        let w__15 ← (( do
          if (((HaveEL EL3) : Bool) : Bool)
          then
            (do
              let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_SCR_EL3_Type_API w__14) == 0#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let TrapEL3 := (w__15 : Bool)
        (pure ((Enable, TrapEL2, TrapEL3))))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__16 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let Enable := ((_get_SCTLR_EL1_Type_EnIA w__16) : (BitVec 1))
            let w__19 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_API w__18) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL2 := (w__19 : Bool)
            let w__21 ← (( do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  let w__20 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_SCR_EL3_Type_API w__20) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL3 := (w__21 : Bool)
            (pure ((Enable, TrapEL2, TrapEL3))))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__22 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                let Enable := ((_get_SCTLR_EL2_Type_EnIA w__22) : (BitVec 1))
                let TrapEL2 : Bool := false
                let w__24 ← (( do
                  if (((HaveEL EL3) : Bool) : Bool)
                  then
                    (do
                      let w__23 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((((_get_SCR_EL3_Type_API w__23) == 0#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let TrapEL3 := (w__24 : Bool)
                (pure ((Enable, TrapEL2, TrapEL3))))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    let w__25 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
                    let Enable := ((_get_SCTLR_EL3_Type_EnIA w__25) : (BitVec 1))
                    let TrapEL2 : Bool := false
                    let TrapEL3 : Bool := false
                    (pure ((Enable, TrapEL2, TrapEL3))))
                else (pure ((Enable, TrapEL2, TrapEL3)))))) ) : SailM ((BitVec 1) × Bool × Bool) )
  if ((Enable == 0#1) : Bool)
  then (pure (x))
  else
    (do
      let w__27 ← (( do
        if ((TrapEL3 : Bool) : Bool)
        then
          (do
            (EL3SDDUndefPriority ()))
        else (pure false) ) : SailM Bool )
      if (w__27 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if (TrapEL2 : Bool)
          then
            (do
              (TrapPACUse EL2)
              (undefined_bitvector_at (← occLabel 1303) 64))
          else
            (do
              if (TrapEL3 : Bool)
              then
                (do
                  let w__30 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
                  if (w__30 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (TrapPACUse EL3)
                      (undefined_bitvector_at (← occLabel 1302) 64)))
              else
                (do
                  (AddPAC x y APIAKey_EL1 false)))))


def AddPACIB (x : (BitVec 64)) (y : (BitVec 64)) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool_at (← occLabel 1304) ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool_at (← occLabel 1305) ()) ) : SailM Bool )
  let Enable ← (( do (undefined_bitvector_at (← occLabel 1306) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do readReg APIBKeyHi_EL1 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg APIBKeyLo_EL1 ) : SailM (BitVec 64) )
  let APIBKey_EL1 : (BitVec 128) :=
    ((Sail.BitVec.extractLsb w__0 63 0) +++ (Sail.BitVec.extractLsb w__1 63 0))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__2.EL
  let (Enable, TrapEL2, TrapEL3) ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (do
        let w__3 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
        let IsEL1Regime : Bool := (w__3 == EL1)
        let w__6 ← (( do
          if (IsEL1Regime : Bool)
          then
            (do
              let w__4 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL1_Type_EnIB w__4))))
          else
            (do
              let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL2_Type_EnIB w__5)))) ) : SailM (BitVec 1) )
        let Enable := (w__6 : (BitVec 1))
        let w__13 ← (( do
          if ((← do
               if ((← do
                    (EL2Enabled ())) : Bool)
               then
                 (do
                   let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_API w__8) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_TGE w__10) == 0#1) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_E2H w__11) == 0#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let TrapEL2 := (w__13 : Bool)
        let w__15 ← (( do
          if (((HaveEL EL3) : Bool) : Bool)
          then
            (do
              let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_SCR_EL3_Type_API w__14) == 0#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let TrapEL3 := (w__15 : Bool)
        (pure ((Enable, TrapEL2, TrapEL3))))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__16 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let Enable := ((_get_SCTLR_EL1_Type_EnIB w__16) : (BitVec 1))
            let w__19 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_API w__18) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL2 := (w__19 : Bool)
            let w__21 ← (( do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  let w__20 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_SCR_EL3_Type_API w__20) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL3 := (w__21 : Bool)
            (pure ((Enable, TrapEL2, TrapEL3))))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__22 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                let Enable := ((_get_SCTLR_EL2_Type_EnIB w__22) : (BitVec 1))
                let TrapEL2 : Bool := false
                let w__24 ← (( do
                  if (((HaveEL EL3) : Bool) : Bool)
                  then
                    (do
                      let w__23 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((((_get_SCR_EL3_Type_API w__23) == 0#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let TrapEL3 := (w__24 : Bool)
                (pure ((Enable, TrapEL2, TrapEL3))))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    let w__25 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
                    let Enable := ((_get_SCTLR_EL3_Type_EnIB w__25) : (BitVec 1))
                    let TrapEL2 : Bool := false
                    let TrapEL3 : Bool := false
                    (pure ((Enable, TrapEL2, TrapEL3))))
                else (pure ((Enable, TrapEL2, TrapEL3)))))) ) : SailM ((BitVec 1) × Bool × Bool) )
  if ((Enable == 0#1) : Bool)
  then (pure (x))
  else
    (do
      let w__27 ← (( do
        if ((TrapEL3 : Bool) : Bool)
        then
          (do
            (EL3SDDUndefPriority ()))
        else (pure false) ) : SailM Bool )
      if (w__27 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if (TrapEL2 : Bool)
          then
            (do
              (TrapPACUse EL2)
              (undefined_bitvector_at (← occLabel 1308) 64))
          else
            (do
              if (TrapEL3 : Bool)
              then
                (do
                  let w__30 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
                  if (w__30 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (TrapPACUse EL3)
                      (undefined_bitvector_at (← occLabel 1307) 64)))
              else
                (do
                  (AddPAC x y APIBKey_EL1 false)))))


def AddPACDA (x : (BitVec 64)) (y : (BitVec 64)) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool_at (← occLabel 1309) ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool_at (← occLabel 1310) ()) ) : SailM Bool )
  let Enable ← (( do (undefined_bitvector_at (← occLabel 1311) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do readReg APDAKeyHi_EL1 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg APDAKeyLo_EL1 ) : SailM (BitVec 64) )
  let APDAKey_EL1 : (BitVec 128) :=
    ((Sail.BitVec.extractLsb w__0 63 0) +++ (Sail.BitVec.extractLsb w__1 63 0))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__2.EL
  let (Enable, TrapEL2, TrapEL3) ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (do
        let w__3 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
        let IsEL1Regime : Bool := (w__3 == EL1)
        let w__6 ← (( do
          if (IsEL1Regime : Bool)
          then
            (do
              let w__4 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL1_Type_EnDA w__4))))
          else
            (do
              let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL2_Type_EnDA w__5)))) ) : SailM (BitVec 1) )
        let Enable := (w__6 : (BitVec 1))
        let w__13 ← (( do
          if ((← do
               if ((← do
                    (EL2Enabled ())) : Bool)
               then
                 (do
                   let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_API w__8) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_TGE w__10) == 0#1) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_E2H w__11) == 0#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let TrapEL2 := (w__13 : Bool)
        let w__15 ← (( do
          if (((HaveEL EL3) : Bool) : Bool)
          then
            (do
              let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_SCR_EL3_Type_API w__14) == 0#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let TrapEL3 := (w__15 : Bool)
        (pure ((Enable, TrapEL2, TrapEL3))))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__16 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let Enable := ((_get_SCTLR_EL1_Type_EnDA w__16) : (BitVec 1))
            let w__19 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_API w__18) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL2 := (w__19 : Bool)
            let w__21 ← (( do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  let w__20 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_SCR_EL3_Type_API w__20) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL3 := (w__21 : Bool)
            (pure ((Enable, TrapEL2, TrapEL3))))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__22 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                let Enable := ((_get_SCTLR_EL2_Type_EnDA w__22) : (BitVec 1))
                let TrapEL2 : Bool := false
                let w__24 ← (( do
                  if (((HaveEL EL3) : Bool) : Bool)
                  then
                    (do
                      let w__23 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((((_get_SCR_EL3_Type_API w__23) == 0#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let TrapEL3 := (w__24 : Bool)
                (pure ((Enable, TrapEL2, TrapEL3))))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    let w__25 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
                    let Enable := ((_get_SCTLR_EL3_Type_EnDA w__25) : (BitVec 1))
                    let TrapEL2 : Bool := false
                    let TrapEL3 : Bool := false
                    (pure ((Enable, TrapEL2, TrapEL3))))
                else (pure ((Enable, TrapEL2, TrapEL3)))))) ) : SailM ((BitVec 1) × Bool × Bool) )
  if ((Enable == 0#1) : Bool)
  then (pure (x))
  else
    (do
      let w__27 ← (( do
        if ((TrapEL3 : Bool) : Bool)
        then
          (do
            (EL3SDDUndefPriority ()))
        else (pure false) ) : SailM Bool )
      if (w__27 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if (TrapEL2 : Bool)
          then
            (do
              (TrapPACUse EL2)
              (undefined_bitvector_at (← occLabel 1313) 64))
          else
            (do
              if (TrapEL3 : Bool)
              then
                (do
                  let w__30 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
                  if (w__30 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (TrapPACUse EL3)
                      (undefined_bitvector_at (← occLabel 1312) 64)))
              else
                (do
                  (AddPAC x y APDAKey_EL1 true)))))


def AddPACDB (x : (BitVec 64)) (y : (BitVec 64)) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool_at (← occLabel 1314) ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool_at (← occLabel 1315) ()) ) : SailM Bool )
  let Enable ← (( do (undefined_bitvector_at (← occLabel 1316) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do readReg APDBKeyHi_EL1 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg APDBKeyLo_EL1 ) : SailM (BitVec 64) )
  let APDBKey_EL1 : (BitVec 128) :=
    ((Sail.BitVec.extractLsb w__0 63 0) +++ (Sail.BitVec.extractLsb w__1 63 0))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__2.EL
  let (Enable, TrapEL2, TrapEL3) ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (do
        let w__3 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
        let IsEL1Regime : Bool := (w__3 == EL1)
        let w__6 ← (( do
          if (IsEL1Regime : Bool)
          then
            (do
              let w__4 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL1_Type_EnDB w__4))))
          else
            (do
              let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL2_Type_EnDB w__5)))) ) : SailM (BitVec 1) )
        let Enable := (w__6 : (BitVec 1))
        let w__13 ← (( do
          if ((← do
               if ((← do
                    (EL2Enabled ())) : Bool)
               then
                 (do
                   let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_API w__8) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_TGE w__10) == 0#1) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_E2H w__11) == 0#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let TrapEL2 := (w__13 : Bool)
        let w__15 ← (( do
          if (((HaveEL EL3) : Bool) : Bool)
          then
            (do
              let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_SCR_EL3_Type_API w__14) == 0#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let TrapEL3 := (w__15 : Bool)
        (pure ((Enable, TrapEL2, TrapEL3))))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__16 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let Enable := ((_get_SCTLR_EL1_Type_EnDB w__16) : (BitVec 1))
            let w__19 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_API w__18) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL2 := (w__19 : Bool)
            let w__21 ← (( do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  let w__20 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_SCR_EL3_Type_API w__20) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL3 := (w__21 : Bool)
            (pure ((Enable, TrapEL2, TrapEL3))))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__22 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                let Enable := ((_get_SCTLR_EL2_Type_EnDB w__22) : (BitVec 1))
                let TrapEL2 : Bool := false
                let w__24 ← (( do
                  if (((HaveEL EL3) : Bool) : Bool)
                  then
                    (do
                      let w__23 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((((_get_SCR_EL3_Type_API w__23) == 0#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let TrapEL3 := (w__24 : Bool)
                (pure ((Enable, TrapEL2, TrapEL3))))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    let w__25 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
                    let Enable := ((_get_SCTLR_EL3_Type_EnDB w__25) : (BitVec 1))
                    let TrapEL2 : Bool := false
                    let TrapEL3 : Bool := false
                    (pure ((Enable, TrapEL2, TrapEL3))))
                else (pure ((Enable, TrapEL2, TrapEL3)))))) ) : SailM ((BitVec 1) × Bool × Bool) )
  if ((Enable == 0#1) : Bool)
  then (pure (x))
  else
    (do
      let w__27 ← (( do
        if ((TrapEL3 : Bool) : Bool)
        then
          (do
            (EL3SDDUndefPriority ()))
        else (pure false) ) : SailM Bool )
      if (w__27 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if (TrapEL2 : Bool)
          then
            (do
              (TrapPACUse EL2)
              (undefined_bitvector_at (← occLabel 1318) 64))
          else
            (do
              if (TrapEL3 : Bool)
              then
                (do
                  let w__30 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
                  if (w__30 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (TrapPACUse EL3)
                      (undefined_bitvector_at (← occLabel 1317) 64)))
              else
                (do
                  (AddPAC x y APDBKey_EL1 true)))))


def AddPACGA (x : (BitVec 64)) (y : (BitVec 64)) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool_at (← occLabel 1319) ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool_at (← occLabel 1320) ()) ) : SailM Bool )
  let isgeneric : Bool := true
  let w__0 ← (( do readReg APGAKeyHi_EL1 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg APGAKeyLo_EL1 ) : SailM (BitVec 64) )
  let APGAKey_EL1 : (BitVec 128) :=
    ((Sail.BitVec.extractLsb w__0 63 0) +++ (Sail.BitVec.extractLsb w__1 63 0))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__2.EL
  let (TrapEL2, TrapEL3) ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (do
        let w__9 ← (( do
          if ((← do
               if ((← do
                    (EL2Enabled ())) : Bool)
               then
                 (do
                   let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_API w__4) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_TGE w__6) == 0#1) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_E2H w__7) == 0#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let TrapEL2 := (w__9 : Bool)
        let w__11 ← (( do
          if (((HaveEL EL3) : Bool) : Bool)
          then
            (do
              let w__10 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_SCR_EL3_Type_API w__10) == 0#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let TrapEL3 := (w__11 : Bool)
        (pure ((TrapEL2, TrapEL3))))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__14 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_API w__13) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL2 := (w__14 : Bool)
            let w__16 ← (( do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  let w__15 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_SCR_EL3_Type_API w__15) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL3 := (w__16 : Bool)
            (pure ((TrapEL2, TrapEL3))))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let TrapEL2 : Bool := false
                let w__18 ← (( do
                  if (((HaveEL EL3) : Bool) : Bool)
                  then
                    (do
                      let w__17 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((((_get_SCR_EL3_Type_API w__17) == 0#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let TrapEL3 := (w__18 : Bool)
                (pure ((TrapEL2, TrapEL3))))
            else
              (let (TrapEL2, TrapEL3) : (Bool × Bool) :=
                if ((questionMark == EL3) : Bool)
                then
                  (let TrapEL2 : Bool := false
                  let TrapEL3 : Bool := false
                  (TrapEL2, TrapEL3))
                else (TrapEL2, TrapEL3)
              (pure ((TrapEL2, TrapEL3)))))) ) : SailM (Bool × Bool) )
  let w__20 ← (( do
    if ((TrapEL3 : Bool) : Bool)
    then
      (do
        (EL3SDDUndefPriority ()))
    else (pure false) ) : SailM Bool )
  if (w__20 : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if (TrapEL2 : Bool)
      then
        (do
          (TrapPACUse EL2)
          (undefined_bitvector_at (← occLabel 1322) 64))
      else
        (do
          if (TrapEL3 : Bool)
          then
            (do
              let w__23 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
              if (w__23 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  (TrapPACUse EL3)
                  (undefined_bitvector_at (← occLabel 1321) 64)))
          else
            (do
              let w__27 ← (( do
                (ComputePAC x y (Sail.BitVec.extractLsb APGAKey_EL1 127 64)
                  (Sail.BitVec.extractLsb APGAKey_EL1 63 0) isgeneric) ) : SailM (BitVec 64) )
              (pure (((Sail.BitVec.extractLsb w__27 63 32) +++ (Zeros (n := 32))))))))


end ArmFull.Functions
