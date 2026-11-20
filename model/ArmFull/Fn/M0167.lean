module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0108
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0150
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152 set_option backward.proofsInPublic true @[expose] public section

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

def getNumBreakpoints (_ : Unit) : SailM Int := do
  (C27cEnsureDebugConfig ())
  readReg NUM_BREAKPOINTS


def getNumCtxBreakpoints (_ : Unit) : SailM Int := do
  (C27cEnsureDebugConfig ())
  readReg __num_ctx_breakpoints


def getNumWatchpoints (_ : Unit) : SailM Int := do
  (C27cEnsureDebugConfig ())
  readReg NUM_WATCHPOINTS


/-- Type quantifiers: idx : Int, increment_name : Int -/
def PMUEvent__2 (pmuevent : (BitVec 16)) (increment_name : Int) (idx : Int) : SailM Unit := do
  let w__0 ← (( do (HavePMUv3 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (()))
  else
    (do
      let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          ArmFull.assert ((0 ≤b idx) && (idx <b 31)) "sail-inputs/03-v8_base.sail:5380.50-5380.51"
          let w__2 ← (( do (PMEVTYPER_read (Sail.Int.toNatChecked (idx))) ) : SailM (BitVec 32) )
          if (((_get_PMEVTYPER_Type_evtCount w__2) == pmuevent) : Bool)
          then
            (do
              let w__3 ← (( do readReg PMUEventAccumulator ) : SailM (Vector Int 31) )
              let w__4 ← (( do readReg PMUEventAccumulator ) : SailM (Vector Int 31) )
              writeReg PMUEventAccumulator (vectorUpdate w__3 (Sail.Int.toNatChecked (idx))
                ((GetElem?.getElem! w__4 (Sail.Int.toNatChecked (idx))) +i increment_name)))
          else (pure (())))
      else
        (do
          ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "sail-inputs/03-v8_base.sail:5386.50-5386.51"
          let w__5 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
          if (((_get_PMEVTYPER_EL0_Type_evtCount
                 (GetElem?.getElem! w__5 (Sail.Int.toNatChecked (idx)))) == pmuevent) : Bool)
          then
            (do
              ArmFull.assert ((0 ≤b idx) && (idx <b 31)) "sail-inputs/03-v8_base.sail:5388.54-5388.55"
              let w__6 ← (( do readReg PMUEventAccumulator ) : SailM (Vector Int 31) )
              let w__7 ← (( do readReg PMUEventAccumulator ) : SailM (Vector Int 31) )
              writeReg PMUEventAccumulator (vectorUpdate w__6 (Sail.Int.toNatChecked (idx))
                ((GetElem?.getElem! w__7 (Sail.Int.toNatChecked (idx))) +i increment_name)))
          else (pure (()))))


/-- Type quantifiers: width : Nat, width ≥ 0 -/
def ConstrainUnpredictableBits (which : Unpredictable) (width : Nat) : SailM (Constraint × (BitVec width)) := do
  let bounded : Bool :=
    ((BEq.beq which Unpredictable_EL2TIMESTAMP) || ((BEq.beq which Unpredictable_EL1TIMESTAMP) || ((BEq.beq
            which Unpredictable_RESERVEDNSxB) || ((BEq.beq which Unpredictable_RESTCF) || ((BEq.beq
                which Unpredictable_PMSCR_PCT) || ((BEq.beq which Unpredictable_RESDACR) || ((BEq.beq
                    which Unpredictable_RESTEXCB) || (BEq.beq which Unpredictable_RESPRRR))))))))
  if (bounded : Bool)
  then
    (do
      ArmFull.assert (width ≤b 8) "sail-inputs/27-armcert_c27b.sail:632.25-632.26"
      let allowed : (BitVec 256) := (Zeros (n := 256))
      let allowed ← (( do
        let loop_i_lower : Nat := 0
        let loop_i_upper : Nat := 255
        (do
          let mut loop_vars := allowed
          for i in [loop_i_lower:loop_i_upper:1]i do
            let allowed := loop_vars
            loop_vars ← do
              let w__1 ← (( do
                if (((i <b (2 ^i width)) : Bool) : Bool)
                then
                  (do
                    (C27bSimpleAllowed which i))
                else (pure false) ) : SailM Bool )
              let allowed : (BitVec 256) :=
                if (w__1 : Bool)
                then (BitVec.update allowed (Sail.Int.toNatChecked (i)) 1#1)
                else allowed
              (pure (allowed))
          (pure loop_vars)) ) : SailM (BitVec 256) )
      let selected ← (( do (C27bSelect allowed) ) : SailM Int )
      let c ← (( do (undefined_Constraint (← occLabel 544) ()) ) : SailM Constraint )
      (pure ((c, (Sail.BitVec.castWidth (get_slice_int width selected 0))))))
  else
    (do
      let w__2 ← (( do (undefined_Constraint (← occLabel 542) ()) ) : SailM Constraint )
      let w__3 ← (( do
        ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 543)
          (Sail.Int.toNatChecked (width)))) ) : SailM (BitVec width) )
      (pure (((w__2, w__3) : (Constraint × (BitVec width))))))


def PhysicalOffsetIsValid (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (HaveECVExt ()) ) : SailM Bool )
            (pure (((! w__2) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then (pure (false))
      else
        (do
          let w__8 ← (( do
            if ((← do
                 if ((← do
                      (HaveEL EL3)) : Bool)
                 then
                   (do
                     let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                     (pure ((((_get_SCR_EL3_Type_NS w__5) == 1#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__7 ← (( do (EffectiveSCR_EL3_RW ()) ) : SailM (BitVec 1) )
                (pure (((w__7 == 0#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__8 : Bool)
          then (pure (false))
          else
            (do
              let w__11 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    let w__10 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure ((((_get_SCR_EL3_Type_ECVEn w__10) == 0#1) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__11 : Bool)
              then (pure (false))
              else
                (do
                  let w__12 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                  let w__13 : Bool :=
                    if (((_get_CNTHCTL_EL2_Type_ECV w__12) == 0#1) : Bool)
                    then false
                    else true
                  (pure (w__13))))))


def BranchEncCycleCount (_ : Unit) : SailM ((BitVec 1) × (BitVec 14)) := do
  let cc ← (( do (BranchRawCycleCount ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (BRBCycleCountingEnabled ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        (FirstBranchAfterProhibited ())) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure ((1#1, (Zeros (n := 14)))))
  else
    (do
      let E ← (( do (undefined_bitvector_at (← occLabel 569) 6) ) : SailM (BitVec 6) )
      let M ← (( do (undefined_bitvector_at (← occLabel 570) 8) ) : SailM (BitVec 8) )
      let (E, M) ← (( do
        if ((cc <b (2 ^i 8)) : Bool)
        then
          (let E : (BitVec 6) := (Zeros (n := 6))
          let M : (BitVec 8) := (integer_subrange cc 7 0)
          (pure (E, M)))
        else
          (do
            let (E, M) ← (( do
              if ((cc ≥b (2 ^i 20)) : Bool)
              then
                (let E : (BitVec 6) := (Ones (n := 6))
                let M : (BitVec 8) := (Ones (n := 8))
                (pure (E, M)))
              else
                (do
                  let E : (BitVec 6) := (integer_subrange 1 5 0)
                  let (E, cc) ← (( do
                    let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (E, cc) => (pure (cc ≥b (2 ^i 9)))) (E, cc)
                      fun (E, cc) => do
                        (pure (let E : (BitVec 6) := (BitVec.addInt E 1)
                          let cc : Int := (fdiv_int cc 2)
                          (E, cc) : ((BitVec 6) × Int)))
                    (pure loop_vars) ) : SailM ((BitVec 6) × Int) )
                  let cc : Int := cc
                  let M : (BitVec 8) := (integer_subrange cc 7 0)
                  (pure (E, M))) ) : SailM ((BitVec 6) × (BitVec 8)) )
            (pure (E, M))) ) : SailM ((BitVec 6) × (BitVec 8)) )
      (pure ((0#1, (E +++ M)))))


def CurrentInstrSet (_ : Unit) : SailM InstrSet := do
  let result ← (( do (undefined_InstrSet (← occLabel 571) ()) ) : SailM InstrSet )
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 : InstrSet :=
        if ((w__1.T == 0#1) : Bool)
        then InstrSet_A32
        else InstrSet_T32
      (pure ((w__2 : InstrSet))))
  else (pure (InstrSet_A64))


/-- Type quantifiers: N : Nat, List.elem N [32, 64] -/
def GetPSRFromPSTATE (targetELState : ExceptionalOccurrenceTargetState) (N : Nat) : SailM (BitVec N) := do
  let w__1 ← (( do
    (pure ((← do
          (UsingAArch32 ())) && ((BEq.beq targetELState AArch32_NonDebugState) : Bool))) ) : SailM
    Bool )
  if (w__1 : Bool)
  then
    (do
      ArmFull.assert (N == 32) "sail-inputs/03-v8_base.sail:7678.22-7678.23")
  else
    (do
      ArmFull.assert (N == 64) "sail-inputs/03-v8_base.sail:7680.22-7680.23")
  let spsr : (BitVec N) := (Sail.BitVec.castWidth (Zeros (n := N)))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  let spsr :=
    ((Sail.BitVec.updateSubrange spsr 31 28 (w__2.N +++ (w__3.Z +++ (w__4.C +++ w__5.V)))) : (BitVec N))
  let w__6 ← (( do (HavePANExt ()) ) : SailM Bool )
  let spsr ← (( do
    if (w__6 : Bool)
    then
      (do
        let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
        let spsr := ((BitVec.update spsr 22 (Bit w__7.PAN)) : (BitVec N))
        (pure (spsr)))
    else (pure (spsr)) ) : SailM (BitVec N) )
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let spsr := ((BitVec.update spsr 20 (Bit w__8.IL)) : (BitVec N))
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__9.nRW == 1#1) : Bool)
  then
    (do
      let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr := ((BitVec.update spsr 27 (Bit w__10.Q)) : (BitVec N))
      let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr :=
        ((Sail.BitVec.updateSubrange spsr 26 25 (Sail.BitVec.extractLsb w__11.IT 1 0)) : (BitVec N))
      let w__12 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
      let spsr ← (( do
        if (w__12 : Bool)
        then
          (do
            let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
            let spsr := ((BitVec.update spsr 23 (Bit w__13.SSBS)) : (BitVec N))
            (pure (spsr)))
        else (pure (spsr)) ) : SailM (BitVec N) )
      let w__14 ← (( do (HaveDITExt ()) ) : SailM Bool )
      let spsr ← (( do
        if (w__14 : Bool)
        then
          (do
            if ((BEq.beq targetELState AArch32_NonDebugState) : Bool)
            then
              (do
                let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                let spsr := ((BitVec.update spsr 21 (Bit w__15.DIT)) : (BitVec N))
                (pure (spsr)))
            else
              (do
                let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
                let spsr := ((BitVec.update spsr 24 (Bit w__16.DIT)) : (BitVec N))
                (pure (spsr))))
        else (pure (spsr)) ) : SailM (BitVec N) )
      let spsr ← (( do
        if (((BEq.beq targetELState AArch64_NonDebugState) || (BEq.beq targetELState DebugState)) : Bool)
        then
          (do
            let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
            let spsr := ((BitVec.update spsr 21 (Bit w__17.SS)) : (BitVec N))
            (pure (spsr)))
        else (pure (spsr)) ) : SailM (BitVec N) )
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr := ((Sail.BitVec.updateSubrange spsr 19 16 w__18.GE) : (BitVec N))
      let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr :=
        ((Sail.BitVec.updateSubrange spsr 15 10 (Sail.BitVec.extractLsb w__19.IT 7 2)) : (BitVec N))
      let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr := ((BitVec.update spsr 9 (Bit w__20.E)) : (BitVec N))
      let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr :=
        ((Sail.BitVec.updateSubrange spsr 8 6 (w__21.A +++ (w__22.I +++ w__23.F))) : (BitVec N))
      let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr := ((BitVec.update spsr 5 (Bit w__24.T)) : (BitVec N))
      let w__25 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
      ArmFull.assert ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__25.M 4)])) == w__26.nRW) "sail-inputs/03-v8_base.sail:7709.42-7709.43"
      let w__27 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr := ((Sail.BitVec.updateSubrange spsr 4 0 w__27.M) : (BitVec N))
      (pure (spsr)))
  else
    (do
      let w__28 ← (( do (HaveMTEExt ()) ) : SailM Bool )
      let spsr ← (( do
        if (w__28 : Bool)
        then
          (do
            let w__29 ← (( do readReg PSTATE ) : SailM ProcState )
            let spsr := ((BitVec.update spsr 25 (Bit w__29.TCO)) : (BitVec N))
            (pure (spsr)))
        else (pure (spsr)) ) : SailM (BitVec N) )
      let w__30 ← (( do (HaveGCS ()) ) : SailM Bool )
      let spsr ← (( do
        if (w__30 : Bool)
        then
          (do
            ArmFull.assert (34 <b N) "sail-inputs/03-v8_base.sail:7716.38-7716.39"
            let w__31 ← (( do readReg PSTATE ) : SailM ProcState )
            let spsr := ((BitVec.update spsr 34 (Bit w__31.EXLOCK)) : (BitVec N))
            (pure (spsr)))
        else (pure (spsr)) ) : SailM (BitVec N) )
      let w__32 ← (( do (HaveDITExt ()) ) : SailM Bool )
      let spsr ← (( do
        if (w__32 : Bool)
        then
          (do
            let w__33 ← (( do readReg PSTATE ) : SailM ProcState )
            let spsr := ((BitVec.update spsr 24 (Bit w__33.DIT)) : (BitVec N))
            (pure (spsr)))
        else (pure (spsr)) ) : SailM (BitVec N) )
      let w__34 ← (( do (HaveUAOExt ()) ) : SailM Bool )
      let spsr ← (( do
        if (w__34 : Bool)
        then
          (do
            let w__35 ← (( do readReg PSTATE ) : SailM ProcState )
            let spsr := ((BitVec.update spsr 23 (Bit w__35.UAO)) : (BitVec N))
            (pure (spsr)))
        else (pure (spsr)) ) : SailM (BitVec N) )
      let w__36 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr := ((BitVec.update spsr 21 (Bit w__36.SS)) : (BitVec N))
      let w__37 ← (( do (HaveFeatNMI ()) ) : SailM Bool )
      let spsr ← (( do
        if (w__37 : Bool)
        then
          (do
            let w__38 ← (( do readReg PSTATE ) : SailM ProcState )
            let spsr := ((BitVec.update spsr 13 (Bit w__38.ALLINT)) : (BitVec N))
            (pure (spsr)))
        else (pure (spsr)) ) : SailM (BitVec N) )
      let w__39 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
      let spsr ← (( do
        if (w__39 : Bool)
        then
          (do
            let w__40 ← (( do readReg PSTATE ) : SailM ProcState )
            let spsr := ((BitVec.update spsr 12 (Bit w__40.SSBS)) : (BitVec N))
            (pure (spsr)))
        else (pure (spsr)) ) : SailM (BitVec N) )
      let w__41 ← (( do (HaveBTIExt ()) ) : SailM Bool )
      let spsr ← (( do
        if (w__41 : Bool)
        then
          (do
            let w__42 ← (( do readReg PSTATE ) : SailM ProcState )
            let spsr := ((Sail.BitVec.updateSubrange spsr 11 10 w__42.BTYPE) : (BitVec N))
            (pure (spsr)))
        else (pure (spsr)) ) : SailM (BitVec N) )
      let w__43 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__44 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__45 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__46 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr :=
        ((Sail.BitVec.updateSubrange spsr 9 6 (w__43.D +++ (w__44.A +++ (w__45.I +++ w__46.F)))) : (BitVec N))
      let w__47 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr := ((BitVec.update spsr 4 (Bit w__47.nRW)) : (BitVec N))
      let w__48 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr := ((Sail.BitVec.updateSubrange spsr 3 2 w__48.EL) : (BitVec N))
      let w__49 ← (( do readReg PSTATE ) : SailM ProcState )
      let spsr := ((BitVec.update spsr 0 (Bit w__49.SP)) : (BitVec N))
      (pure (spsr)))


/-- Type quantifiers: N : Nat, N ≥ 0 -/
def ThisInstrAddr (N : Nat) : SailM (BitVec N) := do
  let w__2 ← (( do
    if (((N == 64) : Bool) : Bool)
    then (pure true)
    else
      (do
        if (((N == 32) : Bool) : Bool)
        then
          (do
            (UsingAArch32 ()))
        else (pure false)) ) : SailM Bool )
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:7754.45-7754.46"
  let w__3 ← (( do readReg _PC ) : SailM (BitVec 64) )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__3 (Sail.Int.toNatChecked ((N -i 1))) 0))))


def IsHighestEL (el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (HighestEL ()) ) : SailM (BitVec 2) )
  (pure ((w__0 == el)))


def AArch64_ExceptionClass (exceptype : Exception) (target_el : (BitVec 2)) : SailM (Int × (BitVec 1)) := do
  let il_is_valid : Bool := true
  let from_32 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  let ec ← (( do (undefined_int_at (← occLabel 671) ()) ) : SailM Int )
  let (ec, il_is_valid) ← (( do
    match exceptype with
    | .Exception_Uncategorized =>
      (let ec : Int := (BitVec.toNat 0x00#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_WFxTrap =>
      (let ec : Int := (BitVec.toNat 0x01#8)
      (pure ((ec, il_is_valid))))
    | .Exception_CP15RTTrap =>
      (do
        let ec : Int := (BitVec.toNat 0x03#8)
        ArmFull.assert from_32 "sail-inputs/03-v8_base.sail:9044.24-9044.25"
        (pure ((ec, il_is_valid))))
    | .Exception_CP15RRTTrap =>
      (do
        let ec : Int := (BitVec.toNat 0x04#8)
        ArmFull.assert from_32 "sail-inputs/03-v8_base.sail:9048.24-9048.25"
        (pure ((ec, il_is_valid))))
    | .Exception_CP14RTTrap =>
      (do
        let ec : Int := (BitVec.toNat 0x05#8)
        ArmFull.assert from_32 "sail-inputs/03-v8_base.sail:9052.24-9052.25"
        (pure ((ec, il_is_valid))))
    | .Exception_CP14DTTrap =>
      (do
        let ec : Int := (BitVec.toNat 0x06#8)
        ArmFull.assert from_32 "sail-inputs/03-v8_base.sail:9056.24-9056.25"
        (pure ((ec, il_is_valid))))
    | .Exception_AdvSIMDFPAccessTrap =>
      (let ec : Int := (BitVec.toNat 0x07#8)
      (pure ((ec, il_is_valid))))
    | .Exception_FPIDTrap =>
      (let ec : Int := (BitVec.toNat 0x08#8)
      (pure ((ec, il_is_valid))))
    | .Exception_PACTrap =>
      (let ec : Int := (BitVec.toNat 0x09#8)
      (pure ((ec, il_is_valid))))
    | .Exception_LDST64BTrap =>
      (let ec : Int := (BitVec.toNat 0x0A#8)
      (pure ((ec, il_is_valid))))
    | .Exception_TSTARTAccessTrap =>
      (let ec : Int := (BitVec.toNat 0x1B#8)
      (pure ((ec, il_is_valid))))
    | .Exception_GPC =>
      (let ec : Int := (BitVec.toNat 0x1E#8)
      (pure ((ec, il_is_valid))))
    | .Exception_CP14RRTTrap =>
      (do
        let ec : Int := (BitVec.toNat 0x0C#8)
        ArmFull.assert from_32 "sail-inputs/03-v8_base.sail:9078.24-9078.25"
        (pure ((ec, il_is_valid))))
    | .Exception_BranchTarget =>
      (let ec : Int := (BitVec.toNat 0x0D#8)
      (pure ((ec, il_is_valid))))
    | .Exception_IllegalState =>
      (let ec : Int := (BitVec.toNat 0x0E#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_SupervisorCall =>
      (let ec : Int := (BitVec.toNat 0x11#8)
      (pure ((ec, il_is_valid))))
    | .Exception_HypervisorCall =>
      (let ec : Int := (BitVec.toNat 0x12#8)
      (pure ((ec, il_is_valid))))
    | .Exception_MonitorCall =>
      (let ec : Int := (BitVec.toNat 0x13#8)
      (pure ((ec, il_is_valid))))
    | .Exception_SystemRegisterTrap =>
      (do
        let ec : Int := (BitVec.toNat 0x18#8)
        ArmFull.assert (! from_32) "sail-inputs/03-v8_base.sail:9098.34-9098.35"
        (pure ((ec, il_is_valid))))
    | .Exception_SystemRegister128Trap =>
      (do
        let ec : Int := (BitVec.toNat 0x14#8)
        ArmFull.assert (! from_32) "sail-inputs/03-v8_base.sail:9102.34-9102.35"
        (pure ((ec, il_is_valid))))
    | .Exception_SVEAccessTrap =>
      (do
        let ec : Int := (BitVec.toNat 0x19#8)
        ArmFull.assert (! from_32) "sail-inputs/03-v8_base.sail:9106.34-9106.35"
        (pure ((ec, il_is_valid))))
    | .Exception_ERetTrap =>
      (do
        let ec : Int := (BitVec.toNat 0x1A#8)
        ArmFull.assert (! from_32) "sail-inputs/03-v8_base.sail:9110.34-9110.35"
        (pure ((ec, il_is_valid))))
    | .Exception_PACFail =>
      (do
        let ec : Int := (BitVec.toNat 0x1C#8)
        ArmFull.assert (! from_32) "sail-inputs/03-v8_base.sail:9114.34-9114.35"
        (pure ((ec, il_is_valid))))
    | .Exception_SMEAccessTrap =>
      (do
        let ec : Int := (BitVec.toNat 0x1D#8)
        ArmFull.assert (! from_32) "sail-inputs/03-v8_base.sail:9118.34-9118.35"
        (pure ((ec, il_is_valid))))
    | .Exception_InstructionAbort =>
      (let ec : Int := (BitVec.toNat 0x20#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_PCAlignment =>
      (let ec : Int := (BitVec.toNat 0x22#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_DataAbort =>
      (let ec : Int := (BitVec.toNat 0x24#8)
      (pure ((ec, il_is_valid))))
    | .Exception_NV2DataAbort =>
      (let ec : Int := (BitVec.toNat 0x25#8)
      (pure ((ec, il_is_valid))))
    | .Exception_SPAlignment =>
      (do
        let ec : Int := (BitVec.toNat 0x26#8)
        let il_is_valid : Bool := false
        ArmFull.assert (! from_32) "sail-inputs/03-v8_base.sail:9137.34-9137.35"
        (pure ((ec, il_is_valid))))
    | .Exception_MemCpyMemSet =>
      (let ec : Int := (BitVec.toNat 0x27#8)
      (pure ((ec, il_is_valid))))
    | .Exception_GCSFail =>
      (do
        let ec : Int := (BitVec.toNat 0x2D#8)
        ArmFull.assert (! from_32) "sail-inputs/03-v8_base.sail:9144.34-9144.35"
        (pure ((ec, il_is_valid))))
    | .Exception_FPTrappedException =>
      (let ec : Int := (BitVec.toNat 0x28#8)
      (pure ((ec, il_is_valid))))
    | .Exception_SError =>
      (let ec : Int := (BitVec.toNat 0x2F#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_Breakpoint =>
      (let ec : Int := (BitVec.toNat 0x30#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_SoftwareStep =>
      (let ec : Int := (BitVec.toNat 0x32#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_Watchpoint =>
      (let ec : Int := (BitVec.toNat 0x34#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_NV2Watchpoint =>
      (let ec : Int := (BitVec.toNat 0x35#8)
      let il_is_valid : Bool := false
      (pure ((ec, il_is_valid))))
    | .Exception_SoftwareBreakpoint =>
      (let ec : Int := (BitVec.toNat 0x38#8)
      (pure ((ec, il_is_valid))))
    | .Exception_VectorCatch =>
      (do
        let ec : Int := (BitVec.toNat 0x3A#8)
        let il_is_valid : Bool := false
        ArmFull.assert from_32 "sail-inputs/03-v8_base.sail:9175.24-9175.25"
        (pure ((ec, il_is_valid))))
    | _ =>
      (do
        (Unreachable ())
        (pure ((ec, il_is_valid)))) ) : SailM (Int × Bool) )
  let w__1 ← (( do
    if ((((ec == (BitVec.toNat 0x20#8)) || (((ec == (BitVec.toNat 0x24#8)) || (((ec == (BitVec.toNat
                 0x30#8)) || (((ec == (BitVec.toNat 0x32#8)) || ((ec == (BitVec.toNat 0x34#8)) : Bool)) : Bool)) : Bool)) : Bool)) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((target_el == w__0.EL) : Bool))))
    else (pure false) ) : SailM Bool )
  let ec : Int :=
    if (w__1 : Bool)
    then (ec +i 1)
    else ec
  let ec : Int :=
    if ((((ec == (BitVec.toNat 0x11#8)) || (((ec == (BitVec.toNat 0x12#8)) || (((ec == (BitVec.toNat
                   0x13#8)) || (((ec == (BitVec.toNat 0x28#8)) || ((ec == (BitVec.toNat 0x38#8)) : Bool)) : Bool)) : Bool)) : Bool)) && (! from_32)) : Bool)
    then (ec +i 4)
    else ec
  let ec : Int := ec
  let il ← (( do (undefined_bitvector_at (← occLabel 672) 1) ) : SailM (BitVec 1) )
  let il ← (( do
    if (il_is_valid : Bool)
    then
      (do
        let w__2 ← (( do (ThisInstrLength ()) ) : SailM Int )
        let w__3 : (BitVec 1) :=
          if ((w__2 == 32) : Bool)
          then 1#1
          else 0#1
        (pure ((w__3 : (BitVec 1)))))
    else (pure (1#1)) ) : SailM (BitVec 1) )
  ArmFull.assert (from_32 || (il == 1#1)) "sail-inputs/03-v8_base.sail:9194.30-9194.31"
  (pure ((ec, il)))


end ArmFull.Functions
