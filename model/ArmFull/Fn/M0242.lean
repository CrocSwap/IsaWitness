import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0023
import ArmFull.Fn.M0034
import ArmFull.Fn.M0040
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0058
import ArmFull.Fn.M0059
import ArmFull.Fn.M0061
import ArmFull.Fn.M0063
import ArmFull.Fn.M0100
import ArmFull.Fn.M0119
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0169
import ArmFull.Fn.M0170
import ArmFull.Fn.M0171
import ArmFull.Fn.M0178
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0197
import ArmFull.Fn.M0202
import ArmFull.Fn.M0228
import ArmFull.Fn.M0236
import ArmFull.Fn.M0237
import ArmFull.Fn.M0238
import ArmFull.Fn.M0239
import ArmFull.Fn.M0240

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

/-- Type quantifiers: k_cold_reset : Bool -/
def AArch64_ResetControlRegisters (cold_reset : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__0 with ZA := 0#1 }
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with SM := 0#1 }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with ALLINT := 0#1 }
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with EXLOCK := 0#1 }
  (ResetControlRegisters cold_reset)
  (pure ((_TLBInvalidate ())))


def SPEToCollectSample (_ : Unit) : SailM Bool := SailME.run do
  let w__0 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
  if ((IsZero (_get_PMSICR_EL1_Type_COUNT w__0)) : Bool)
  then
    (do
      (SPEResetSampleCounter ()))
  else
    (do
      let w__1 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
      let w__2 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
      writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange w__1 31 0
        (BitVec.subInt (_get_PMSICR_EL1_Type_COUNT w__2) 1))
      let w__3 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
      if ((IsZero (_get_PMSICR_EL1_Type_COUNT w__3)) : Bool)
      then
        (do
          let w__6 ← (( do
            if ((← do
                 let w__4 ← (( do readReg PMSIRR_EL1 ) : SailME Bool (BitVec 64) )
                 (pure ((((_get_PMSIRR_EL1_Type_RND w__4) == 1#1) : Bool)))) : Bool)
            then
              (do
                let w__5 ← (( do readReg PMSIDR_EL1 ) : SailME Bool (BitVec 64) )
                (pure ((((_get_PMSIDR_EL1_Type_ERnd w__5) == 1#1) : Bool))))
            else (pure false) ) : SailME Bool Bool )
          if (w__6 : Bool)
          then
            (do
              let w__7 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
              let w__8 ← (( do (SPEGetRandomInterval ()) ) : SailME Bool (BitVec 8) )
              writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange w__7 63 56 w__8))
          else
            (do
              SailME.throw (true : Bool)))
      else (pure (())))
  let w__9 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
  if (((BitVec.toNat (_get_PMSICR_EL1_Type_ECOUNT w__9)) != 0) : Bool)
  then
    (do
      let w__10 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
      let w__11 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
      writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange w__10 63 56
        (BitVec.subInt (_get_PMSICR_EL1_Type_ECOUNT w__11) 1))
      let w__12 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
      if ((IsZero (_get_PMSICR_EL1_Type_ECOUNT w__12)) : Bool)
      then
        (do
          SailME.throw (true : Bool))
      else (pure (())))
  else (pure (()))
  (pure (false))


def SPESampleMemCopy (_ : Unit) : SailM Unit := do
  let loads_pass_filter ← (( do
    if ((← do
         let w__0 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
         (pure ((((_get_PMSFCR_EL1_Type_FT w__0) == 1#1) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_PMSFCR_EL1_Type_LD w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let stores_pass_filter ← (( do
    if ((← do
         let w__2 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
         (pure ((((_get_PMSFCR_EL1_Type_FT w__2) == 1#1) : Bool)))) : Bool)
    then
      (do
        let w__3 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_PMSFCR_EL1_Type_ST w__3) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let record_load ← (( do (undefined_bool_at (← occLabel 2449) ()) ) : SailM Bool )
  let record_load ← (( do
    if ((loads_pass_filter && (! stores_pass_filter)) : Bool)
    then (pure (true))
    else
      (do
        if (((! loads_pass_filter) && stores_pass_filter) : Bool)
        then (pure (false))
        else
          (do
            (SPEGetRandomBoolean ()))) ) : SailM Bool )
  writeReg SPESampleClass 0b01#2
  let ldst : (BitVec 1) :=
    if (record_load : Bool)
    then 0#1
    else 1#1
  let w__5 ← (( do readReg SPESampleSubclass ) : SailM (BitVec 8) )
  writeReg SPESampleSubclass (Sail.BitVec.updateSubrange w__5 7 0 (0b0010000#7 +++ ldst))
  writeReg SPESampleSubclassValid true
  writeReg SPESampleOpType (if (record_load : Bool)
  then OpType_Load
  else OpType_Store)


def BRBEISB (_ : Unit) : SailM Unit := do
  let branch_conditional : Bool := false
  let w__0 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
  (BRBEBranch BranchType_DIR branch_conditional (BitVec.addInt w__0 4))


def DRPSInstruction (_ : Unit) : SailM Unit := do
  let _ : Unit := (SynchronizeContext ())
  let sync_errors ← (( do
    if ((← do
         (HaveIESB ())) : Bool)
    then
      (do
        let w__1 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
        (pure ((((_get_SCTLRType_IESB w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__4 ← (( do
    if ((← do
         (HaveDoubleFaultExt ())) : Bool)
    then
      (do
        let w__3 ← (( do (UsingAArch32 ()) ) : SailM Bool )
        (pure (((! w__3) : Bool))))
    else (pure false) ) : SailM Bool )
  let sync_errors ← (( do
    if (w__4 : Bool)
    then
      (do
        if ((sync_errors : Bool) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      let w__5 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
                      (pure (((w__5 == 1#1) : Bool)))) : Bool)
                 then
                   (do
                     let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                     (pure ((((_get_SCR_EL3_Type_NMEA w__6) == 1#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__8.EL == EL3) : Bool))))
            else (pure false)))
    else (pure (sync_errors)) ) : SailM Bool )
  let w__11 ← (( do (ConstrainUnpredictableBool Unpredictable_IESBinDebug) ) : SailM Bool )
  let sync_errors : Bool :=
    if ((! w__11) : Bool)
    then false
    else sync_errors
  let _ : Unit :=
    if (sync_errors : Bool)
    then (SynchronizeErrors ())
    else ()
  (DebugRestorePSR ())


/-- Type quantifiers: k_linked_to : Bool, n_in : Int -/
def AArch32_BreakpointValueMatch (n_in : Int) (vaddress : (BitVec 32)) (linked_to : Bool) : SailM (Bool × Bool) := SailME.run do
  let n : Int := n_in
  let c ← (( do (undefined_Constraint (← occLabel 2649) ()) ) : SailME (Bool × Bool) Constraint
    )
  let w__0 ← (( do (NumBreakpointsImplemented ()) ) : SailME (Bool × Bool) Int )
  let (c, n) ← (( do
    if ((n ≥b w__0) : Bool)
    then
      (do
        let w__1 ← (( do (NumBreakpointsImplemented ()) ) : SailME (Bool × Bool) Int )
        let w__2 ← (( do (ConstrainUnpredictableInteger 0 (w__1 -i 1) Unpredictable_BPNOTIMPL) ) :
          SailME (Bool × Bool) (Constraint × Int) )
        let (tup__0, tup__1) := (w__2 : (Constraint × Int))
        let c : Constraint := tup__0
        let n : Int := tup__1
        ArmFull.assert ((BEq.beq c Constraint_DISABLED) || (BEq.beq c Constraint_UNKNOWN)) "sail-arm/v8_base.sail:40261.65-40261.66"
        if ((BEq.beq c Constraint_DISABLED) : Bool)
        then
          (do
            SailME.throw ((false, false) : (Bool × Bool)))
        else (pure (()))
        (pure ((c, n))))
    else (pure ((c, n))) ) : SailME (Bool × Bool) (Constraint × Int) )
  let n : Int := n
  ArmFull.assert ((0 ≤b n) && (n <b 16)) "sail-arm/v8_base.sail:40268.42-40268.43"
  let w__3 ← (( do (DBGBCR_read (Sail.Int.toNatChecked (n))) ) : SailME (Bool × Bool) (BitVec 32)
    )
  if (((_get_DBGBCR_Type_E w__3) == 0#1) : Bool)
  then (pure ((false, false)))
  else
    (do
      let w__4 ← (( do (DBGBCR_read (Sail.Int.toNatChecked (n))) ) : SailME (Bool × Bool)
        (BitVec 32) )
      let dbgtype : (BitVec 4) := (_get_DBGBCR_Type_BT w__4)
      let w__5 ← (( do (AArch32_ReservedBreakpointType n dbgtype) ) : SailME (Bool × Bool)
        (Constraint × (BitVec 4)) )
      let (tup__0, tup__1) := (w__5 : (Constraint × (BitVec 4)))
      let c : Constraint := tup__0
      let dbgtype : (BitVec 4) := tup__1
      if ((BEq.beq c Constraint_DISABLED) : Bool)
      then (pure ((false, false)))
      else
        (do
          let b__5 := dbgtype
          let match_addr : Bool :=
            (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__5 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     b__5 1 1)) == (0#1 : (BitVec 1)))) : Bool)
            then true
            else false : Bool)
          let b__4 := dbgtype
          let mismatch : Bool :=
            (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__4 3 1)) == (0b010#3 : (BitVec 3))) : Bool)
            then true
            else false : Bool)
          let b__3 := dbgtype
          let match_vmid : Bool :=
            (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__3 3 2)) == (0b10#2 : (BitVec 2))) : Bool)
            then true
            else false : Bool)
          let b__2 := dbgtype
          let match_cid1 : Bool :=
            (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 1 1)) == (1#1 : (BitVec 1))) : Bool)
            then true
            else false : Bool)
          let b__1 := dbgtype
          let match_cid2 : Bool :=
            (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 3 2)) == (0b11#2 : (BitVec 2))) : Bool)
            then true
            else false : Bool)
          let b__0 := dbgtype
          let linking_enabled : Bool :=
            (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (1#1 : (BitVec 1))) : Bool)
            then true
            else false : Bool)
          if ((linked_to && (! linking_enabled)) : Bool)
          then
            (do
              let w__6 ← (( do (ConstrainUnpredictableBool Unpredictable_BPLINKINGDISABLED) ) :
                SailME (Bool × Bool) Bool )
              if ((! w__6) : Bool)
              then
                (do
                  SailME.throw ((false, false) : (Bool × Bool)))
              else (pure (())))
          else (pure (()))
          if ((((! linked_to) && linking_enabled) && (! match_addr)) : Bool)
          then (pure ((false, false)))
          else
            (do
              let bvr_match : Bool := false
              let bxvr_match : Bool := false
              let bvr_match ← (( do
                if (match_addr : Bool)
                then
                  (do
                    let byte : Int := (BitVec.toNat (Sail.BitVec.extractLsb vaddress 1 0))
                    ArmFull.assert ((byte == 0) || (byte == 2)) "sail-arm/v8_base.sail:40314.36-40314.37"
                    let w__7 ← (( do (DBGBCR_read (Sail.Int.toNatChecked (n))) ) : SailME
                      (Bool × Bool) (BitVec 32) )
                    let byte_select_match : Bool :=
                      ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (_get_DBGBCR_Type_BAS w__7)
                            (Sail.Int.toNatChecked (byte)))])) == 1#1)
                    let top : Nat := 31
                    (pure ((← do
                          let w__8 ← (( do (DBGBVR_read (Sail.Int.toNatChecked (n))) ) : SailME
                            (Bool × Bool) (BitVec 32) )
                          (pure ((((Sail.BitVec.castWidth (m := ((Sail.Int.toNatChecked top) - 1)) (Sail.BitVec.extractLsb
                                vaddress top 2)) == (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                                w__8 top 2))) : Bool)))) && byte_select_match)))
                else
                  (do
                    if (match_cid1 : Bool)
                    then
                      (do
                        if ((← do
                             let w__10 ← (( do readReg PSTATE ) : SailME (Bool × Bool) ProcState
                               )
                             (pure (((w__10.EL != EL2) : Bool)))) : Bool)
                        then
                          (do
                            let w__11 ← (( do (CONTEXTIDR_read ()) ) : SailME (Bool × Bool)
                              (BitVec 32) )
                            let w__12 ← (( do (DBGBVR_read (Sail.Int.toNatChecked (n))) ) : SailME
                              (Bool × Bool) (BitVec 32) )
                            (pure (((w__11 == (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                                  w__12 31 0))) : Bool))))
                        else (pure false))
                    else (pure (bvr_match))) ) : SailME (Bool × Bool) Bool )
              let bxvr_match ← (( do
                if (match_vmid : Bool)
                then
                  (do
                    let vmid ← (( do (undefined_bitvector_at (← occLabel 2650) 16) ) : SailME
                      (Bool × Bool) (BitVec 16) )
                    let bvr_vmid ← (( do (undefined_bitvector_at (← occLabel 2651) 16) ) :
                      SailME (Bool × Bool) (BitVec 16) )
                    let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailME (Bool × Bool) Bool )
                    let (bvr_vmid, vmid) ← (( do
                      if (w__14 : Bool)
                      then
                        (do
                          let w__15 ← (( do readReg VTTBR ) : SailME (Bool × Bool) (BitVec 64) )
                          let vmid :=
                            ((Sail.BitVec.zeroExtend (_get_VTTBR_Type_VMID w__15) 16) : (BitVec 16))
                          let w__16 ← (( do (DBGBXVR_read (Sail.Int.toNatChecked (n))) ) : SailME
                            (Bool × Bool) (BitVec 32) )
                          let bvr_vmid :=
                            ((Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb w__16 7 0) 16) : (BitVec 16))
                          (pure ((bvr_vmid, vmid))))
                      else
                        (do
                          let w__19 ← (( do
                            if ((← do
                                 let w__17 ← (( do (Have16bitVMID ()) ) : SailME (Bool × Bool)
                                   Bool )
                                 (pure (((! w__17) : Bool)))) : Bool)
                            then (pure true)
                            else
                              (do
                                let w__18 ← (( do readReg VTCR_EL2 ) : SailME (Bool × Bool)
                                  (BitVec 64) )
                                (pure ((((_get_VTCR_EL2_Type_VS w__18) == 0#1) : Bool)))) ) : SailME
                            (Bool × Bool) Bool )
                          if (w__19 : Bool)
                          then
                            (do
                              let w__20 ← (( do (VTTBR_EL2_read ()) ) : SailME (Bool × Bool)
                                (BitVec 128) )
                              let vmid :=
                                ((Sail.BitVec.zeroExtend
                                  (Sail.BitVec.extractLsb (_get_VTTBR_EL2_Type_VMID w__20) 7 0) 16) : (BitVec 16))
                              let w__21 ← (( do (DBGBXVR_read (Sail.Int.toNatChecked (n))) ) :
                                SailME (Bool × Bool) (BitVec 32) )
                              let bvr_vmid :=
                                ((Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb w__21 7 0) 16) : (BitVec 16))
                              (pure ((bvr_vmid, vmid))))
                          else
                            (do
                              let w__22 ← (( do (VTTBR_EL2_read ()) ) : SailME (Bool × Bool)
                                (BitVec 128) )
                              let vmid := ((_get_VTTBR_EL2_Type_VMID w__22) : (BitVec 16))
                              let w__23 ← (( do (DBGBXVR_read (Sail.Int.toNatChecked (n))) ) :
                                SailME (Bool × Bool) (BitVec 32) )
                              let bvr_vmid := ((Sail.BitVec.extractLsb w__23 15 0) : (BitVec 16))
                              (pure ((bvr_vmid, vmid))))) ) : SailME (Bool × Bool)
                      ((BitVec 16) × (BitVec 16)) )
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    let w__24 ← (( do readReg PSTATE ) : SailME (Bool × Bool)
                                      ProcState )
                                    (pure (((w__24.EL == EL0) : Bool)))) : Bool)
                               then (pure true)
                               else
                                 (do
                                   let w__25 ← (( do readReg PSTATE ) : SailME (Bool × Bool)
                                     ProcState )
                                   (pure (((w__25.EL == EL1) : Bool))))) : Bool)
                          then
                            (do
                              (EL2Enabled ()))
                          else (pure false)) && ((vmid == bvr_vmid) : Bool))))
                else
                  (do
                    if (match_cid2 : Bool)
                    then
                      (do
                        if ((← do
                             if ((← do
                                  if ((← do
                                       let w__30 ← (( do readReg PSTATE ) : SailME (Bool × Bool)
                                         ProcState )
                                       (pure (((w__30.EL != EL3) : Bool)))) : Bool)
                                  then
                                    (do
                                      (EL2Enabled ()))
                                  else (pure false)) : Bool)
                             then
                               (do
                                 let w__33 ← (( do (ELUsingAArch32 EL2) ) : SailME (Bool × Bool)
                                   Bool )
                                 (pure (((! w__33) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__35 ← (( do (DBGBXVR_read (Sail.Int.toNatChecked (n))) ) :
                              SailME (Bool × Bool) (BitVec 32) )
                            let w__36 ← (( do readReg CONTEXTIDR_EL2 ) : SailME (Bool × Bool)
                              (BitVec 64) )
                            (pure ((((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb w__35
                                  31 0)) == (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                                  w__36 31 0))) : Bool))))
                        else (pure false))
                    else (pure (bxvr_match))) ) : SailME (Bool × Bool) Bool )
              let bvr_match_valid : Bool := (match_addr || match_cid1)
              let bxvr_match_valid : Bool := (match_vmid || match_cid2)
              let val_match : Bool :=
                (((! bxvr_match_valid) || bxvr_match) && ((! bvr_match_valid) || bvr_match))
              (pure (((val_match && (! mismatch)), ((! val_match) && mismatch)))))))


/-- Type quantifiers: k_cold_reset : Bool -/
def AArch32_ResetControlRegisters (cold_reset : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__0 with SS := 0#1 }
  (ResetControlRegisters cold_reset)
  (pure ((_TLBInvalidate ())))


def gic_write_ram (offset : (BitVec 16)) (data : (BitVec 32)) : SailM Unit := do
  let accdesc ← (( do (CreateAccDescGPR MemOp_STORE false true false) ) : SailM AccessDescriptor )
  let pa := (Sail.BitVec.zeroExtend (GIC_BASE +++ offset) 56)
  let w__0 ← (( do
    (sail_mem_write (write_request accdesc none 4 (Sail.BitVec.zeroExtend pa 64) pa data)) ) : SailM
    (Result (Option Bool) Fault) )
  match w__0 with
  | .Ok _ => (pure (()))
  | .Err _ =>
    (do
      ArmFull.assert false "sail-arm/devices.sail:145.26-145.27"
      throw Error.Exit)


def decode_aarch32_instrs_DCPS1_T1enc_A_txt (_ : Unit) : SailM Unit := do
  (execute_aarch32_instrs_DCPS1_Op_A_txt ())


def decode_aarch32_instrs_DCPS2_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((! (HaveEL EL2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch32_instrs_DCPS2_Op_A_txt ())


def decode_aarch32_instrs_DCPS3_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((! (HaveEL EL3)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch32_instrs_DCPS3_Op_A_txt ())


def execute_aarch64_instrs_system_exceptions_debug_exception (target_level : (BitVec 2)) : SailM Unit := do
  (DCPSInstruction target_level)


/-- Type quantifiers: pc : Int -/
def __DecodeA64_DataProcImm (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__1 ← (( do
    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 30 23)) == (0x22#8 : (BitVec 8))) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__0 <b 18) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      writeReg SEE 18
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let imm12 := (BitVec.slice __opcode 10 12)
      let sh := (BitVec.slice __opcode 22 1)
      let S := (BitVec.slice __opcode 29 1)
      let op := (BitVec.slice __opcode 30 1)
      let sf := (BitVec.slice __opcode 31 1)
      (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op
        sf))
  else
    (do
      let w__3 ← (( do
        if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 30 23)) == (0x62#8 : (BitVec 8))) : Bool) : Bool)
        then
          (do
            let w__2 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__2 <b 19) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          writeReg SEE 19
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let imm12 := (BitVec.slice __opcode 10 12)
          let sh := (BitVec.slice __opcode 22 1)
          let S := (BitVec.slice __opcode 29 1)
          let op := (BitVec.slice __opcode 30 1)
          let sf := (BitVec.slice __opcode 31 1)
          (decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh
            S op sf))
      else
        (do
          let w__5 ← (( do
            if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 30 23)) == (0xA2#8 : (BitVec 8))) : Bool) : Bool)
            then
              (do
                let w__4 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__4 <b 20) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              writeReg SEE 20
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let imm12 := (BitVec.slice __opcode 10 12)
              let sh := (BitVec.slice __opcode 22 1)
              let S := (BitVec.slice __opcode 29 1)
              let op := (BitVec.slice __opcode 30 1)
              let sf := (BitVec.slice __opcode 31 1)
              (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12
                sh S op sf))
          else
            (do
              let w__7 ← (( do
                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 30 23)) == (0xE2#8 : (BitVec 8))) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 21) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  writeReg SEE 21
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let imm12 := (BitVec.slice __opcode 10 12)
                  let sh := (BitVec.slice __opcode 22 1)
                  let S := (BitVec.slice __opcode 29 1)
                  let op := (BitVec.slice __opcode 30 1)
                  let sf := (BitVec.slice __opcode 31 1)
                  (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn
                    imm12 sh S op sf))
              else
                (do
                  let w__9 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b1001000110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             __opcode 15 14)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                    then
                      (do
                        let w__8 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__8 <b 26) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      writeReg SEE 26
                      let Xd := (BitVec.slice __opcode 0 5)
                      let Xn := (BitVec.slice __opcode 5 5)
                      let uimm4 := (BitVec.slice __opcode 10 4)
                      let op3 := (BitVec.slice __opcode 14 2)
                      let uimm6 := (BitVec.slice __opcode 16 6)
                      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 14)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 15)])) != 0#1)) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_addg_aarch64_instrs_integer_tags_mcaddtag Xd Xn uimm4 op3 uimm6)))
                  else
                    (do
                      let w__11 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                 __opcode 28 24)) == (0b10000#5 : (BitVec 5)))) : Bool) : Bool)
                        then
                          (do
                            let w__10 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__10 <b 34) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__11 : Bool)
                      then
                        (do
                          writeReg SEE 34
                          let Rd := (BitVec.slice __opcode 0 5)
                          let immhi := (BitVec.slice __opcode 5 19)
                          let immlo := (BitVec.slice __opcode 29 2)
                          let op := (BitVec.slice __opcode 31 1)
                          (decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel Rd immhi
                            immlo op))
                      else
                        (do
                          let w__13 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode
                                     31 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                     __opcode 28 24)) == (0b10000#5 : (BitVec 5)))) : Bool) : Bool)
                            then
                              (do
                                let w__12 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__12 <b 35) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__13 : Bool)
                          then
                            (do
                              writeReg SEE 35
                              let Rd := (BitVec.slice __opcode 0 5)
                              let immhi := (BitVec.slice __opcode 5 19)
                              let immlo := (BitVec.slice __opcode 29 2)
                              let op := (BitVec.slice __opcode 31 1)
                              (decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel Rd immhi
                                immlo op))
                          else
                            (do
                              let w__15 ← (( do
                                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                       __opcode 30 23)) == (0x24#8 : (BitVec 8))) : Bool) : Bool)
                                then
                                  (do
                                    let w__14 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__14 <b 40) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__15 : Bool)
                              then
                                (do
                                  writeReg SEE 40
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let imms := (BitVec.slice __opcode 10 6)
                                  let immr := (BitVec.slice __opcode 16 6)
                                  let N := (BitVec.slice __opcode 22 1)
                                  let opc := (BitVec.slice __opcode 29 2)
                                  let sf := (BitVec.slice __opcode 31 1)
                                  (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn
                                    imms immr N opc sf))
                              else
                                (do
                                  let w__17 ← (( do
                                    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                           __opcode 30 23)) == (0xE4#8 : (BitVec 8))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__16 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__16 <b 41) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__17 : Bool)
                                  then
                                    (do
                                      writeReg SEE 41
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let imms := (BitVec.slice __opcode 10 6)
                                      let immr := (BitVec.slice __opcode 16 6)
                                      let N := (BitVec.slice __opcode 22 1)
                                      let opc := (BitVec.slice __opcode 29 2)
                                      let sf := (BitVec.slice __opcode 31 1)
                                      (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate
                                        Rd Rn imms immr N opc sf))
                                  else
                                    (do
                                      let w__19 ← (( do
                                        if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                               __opcode 30 23)) == (0xA4#8 : (BitVec 8))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__18 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__18 <b 42) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__19 : Bool)
                                      then
                                        (do
                                          writeReg SEE 42
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let imms := (BitVec.slice __opcode 10 6)
                                          let immr := (BitVec.slice __opcode 16 6)
                                          let N := (BitVec.slice __opcode 22 1)
                                          let opc := (BitVec.slice __opcode 29 2)
                                          let sf := (BitVec.slice __opcode 31 1)
                                          (decode_eor_log_imm_aarch64_instrs_integer_logical_immediate
                                            Rd Rn imms immr N opc sf))
                                      else
                                        (do
                                          let w__21 ← (( do
                                            if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                   __opcode 30 23)) == (0x64#8 : (BitVec 8))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__20 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__20 <b 43) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__21 : Bool)
                                          then
                                            (do
                                              writeReg SEE 43
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let imms := (BitVec.slice __opcode 10 6)
                                              let immr := (BitVec.slice __opcode 16 6)
                                              let N := (BitVec.slice __opcode 22 1)
                                              let opc := (BitVec.slice __opcode 29 2)
                                              let sf := (BitVec.slice __opcode 31 1)
                                              (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate
                                                Rd Rn imms immr N opc sf))
                                          else
                                            (do
                                              let w__23 ← (( do
                                                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                       __opcode 30 23)) == (0x66#8 : (BitVec 8))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__22 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__22 <b 76) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__23 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 76
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let imms := (BitVec.slice __opcode 10 6)
                                                  let immr := (BitVec.slice __opcode 16 6)
                                                  let N := (BitVec.slice __opcode 22 1)
                                                  let opc := (BitVec.slice __opcode 29 2)
                                                  let sf := (BitVec.slice __opcode 31 1)
                                                  (decode_bfm_aarch64_instrs_integer_bitfield Rd Rn
                                                    imms immr N opc sf))
                                              else
                                                (do
                                                  let w__25 ← (( do
                                                    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                           __opcode 30 23)) == (0x26#8 : (BitVec 8))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__24 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__24 <b 77) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__25 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 77
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let imms := (BitVec.slice __opcode 10 6)
                                                      let immr := (BitVec.slice __opcode 16 6)
                                                      let N := (BitVec.slice __opcode 22 1)
                                                      let opc := (BitVec.slice __opcode 29 2)
                                                      let sf := (BitVec.slice __opcode 31 1)
                                                      (decode_sbfm_aarch64_instrs_integer_bitfield
                                                        Rd Rn imms immr N opc sf))
                                                  else
                                                    (do
                                                      let w__27 ← (( do
                                                        if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                               __opcode 30 23)) == (0xA6#8 : (BitVec 8))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__26 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__26 <b 78) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__27 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 78
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let imms := (BitVec.slice __opcode 10 6)
                                                          let immr := (BitVec.slice __opcode 16 6)
                                                          let N := (BitVec.slice __opcode 22 1)
                                                          let opc := (BitVec.slice __opcode 29 2)
                                                          let sf := (BitVec.slice __opcode 31 1)
                                                          (decode_ubfm_aarch64_instrs_integer_bitfield
                                                            Rd Rn imms immr N opc sf))
                                                      else
                                                        (do
                                                          let w__29 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 30 23)) == (0x27#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 21 21)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__28 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__28 <b 206) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__29 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 206
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let imms :=
                                                                (BitVec.slice __opcode 10 6)
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let N := (BitVec.slice __opcode 22 1)
                                                              let sf := (BitVec.slice __opcode 31 1)
                                                              (decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate
                                                                Rd Rn imms Rm N sf))
                                                          else
                                                            (do
                                                              let w__31 ← (( do
                                                                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                       __opcode 30 23)) == (0xE5#8 : (BitVec 8))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__30 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__30 <b 696) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__31 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 696
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let imm16 :=
                                                                    (BitVec.slice __opcode 5 16)
                                                                  let hw :=
                                                                    (BitVec.slice __opcode 21 2)
                                                                  let opc :=
                                                                    (BitVec.slice __opcode 29 2)
                                                                  let sf :=
                                                                    (BitVec.slice __opcode 31 1)
                                                                  (decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide
                                                                    Rd imm16 hw opc sf))
                                                              else
                                                                (do
                                                                  let w__33 ← (( do
                                                                    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                           __opcode 30 23)) == (0x25#8 : (BitVec 8))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__32 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__32 <b 697) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__33 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 697
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let imm16 :=
                                                                        (BitVec.slice __opcode 5 16)
                                                                      let hw :=
                                                                        (BitVec.slice __opcode 21 2)
                                                                      let opc :=
                                                                        (BitVec.slice __opcode 29 2)
                                                                      let sf :=
                                                                        (BitVec.slice __opcode 31 1)
                                                                      (decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide
                                                                        Rd imm16 hw opc sf))
                                                                  else
                                                                    (do
                                                                      let w__35 ← (( do
                                                                        if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                               __opcode 30 23)) == (0xA5#8 : (BitVec 8))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__34 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__34 <b 698) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__35 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 698
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let imm16 :=
                                                                            (BitVec.slice __opcode 5
                                                                              16)
                                                                          let hw :=
                                                                            (BitVec.slice __opcode
                                                                              21 2)
                                                                          let opc :=
                                                                            (BitVec.slice __opcode
                                                                              29 2)
                                                                          let sf :=
                                                                            (BitVec.slice __opcode
                                                                              31 1)
                                                                          (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide
                                                                            Rd imm16 hw opc sf))
                                                                      else
                                                                        (do
                                                                          let w__37 ← (( do
                                                                            if ((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                   __opcode 30 18)) == (0b0010001110000#13 : (BitVec 13))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__36 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__36 <b 832) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__37 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 832
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let imm8 :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 8)
                                                                              let sf :=
                                                                                (BitVec.slice
                                                                                  __opcode 31 1)
                                                                              (decode_smax_imm_aarch64_instrs_integer_arithmetic_max_min_smax_imm
                                                                                Rd Rn imm8 sf))
                                                                          else
                                                                            (do
                                                                              let w__39 ← (( do
                                                                                if ((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                       __opcode 30
                                                                                       18)) == (0b0010001110010#13 : (BitVec 13))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__38 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__38 <b 847) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__39 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 847
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let imm8 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 8)
                                                                                  let sf :=
                                                                                    (BitVec.slice
                                                                                      __opcode 31 1)
                                                                                  (decode_smin_imm_aarch64_instrs_integer_arithmetic_max_min_smin_imm
                                                                                    Rd Rn imm8 sf))
                                                                              else
                                                                                (do
                                                                                  let w__41 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 22)) == (0b1101000110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 14)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__40 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__40 <b 990) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__41 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 990
                                                                                      let Xd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Xn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let uimm4 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 4)
                                                                                      let op3 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          14 2)
                                                                                      let uimm6 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 6)
                                                                                      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 14)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 15)])) != 0#1)) : Bool)
                                                                                      then
                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                          ()))
                                                                                      else
                                                                                        (do
                                                                                          (decode_subg_aarch64_instrs_integer_tags_mcsubtag
                                                                                            Xd Xn
                                                                                            uimm4
                                                                                            op3
                                                                                            uimm6)))
                                                                                  else
                                                                                    (do
                                                                                      let w__43 ← (( do
                                                                                        if ((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               30 18)) == (0b0010001110001#13 : (BitVec 13))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__42 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__42 <b 1018) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__43 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1018
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let imm8 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 8)
                                                                                          let sf :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              31 1)
                                                                                          (decode_umax_imm_aarch64_instrs_integer_arithmetic_max_min_umax_imm
                                                                                            Rd Rn
                                                                                            imm8 sf))
                                                                                      else
                                                                                        (do
                                                                                          let w__45 ← (( do
                                                                                            if ((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   30
                                                                                                   18)) == (0b0010001110011#13 : (BitVec 13))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__44 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__44 <b 1021) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__45 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1021
                                                                                              let Rd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let imm8 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  8)
                                                                                              let sf :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  31
                                                                                                  1)
                                                                                              (decode_umin_imm_aarch64_instrs_integer_arithmetic_max_min_umin_imm
                                                                                                Rd
                                                                                                Rn
                                                                                                imm8
                                                                                                sf))
                                                                                          else
                                                                                            sailThrow ((Error_Undefined
                                                                                              ()))))))))))))))))))))))))


end ArmFull.Functions
