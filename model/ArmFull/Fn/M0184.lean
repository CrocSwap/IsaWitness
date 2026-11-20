module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182 set_option backward.proofsInPublic true @[expose] public section

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

def AArch32_GeneralExceptionsToAArch64 (_ : Unit) : SailM Bool := do
  if ((← do
       if ((← do
            let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__0.EL == EL0) : Bool)))) : Bool)
       then
         (do
           let w__1 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
           (pure (((! w__1) : Bool))))
       else (pure false)) : Bool)
  then (pure true)
  else
    (do
      if ((← do
           if ((← do
                (EL2Enabled ())) : Bool)
           then
             (do
               let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
               (pure (((! w__4) : Bool))))
           else (pure false)) : Bool)
      then
        (do
          let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
          (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool))))
      else (pure false))


def TestEventCNTP (prev_physical_count : (BitVec 64)) (current_physical_count : (BitVec 64)) : SailM Unit := do
  let n ← (( do (undefined_int_at (.site 1179) ()) ) : SailM Int )
  let offset ← (( do (undefined_bitvector_at (.site 1180) 64) ) : SailM (BitVec 64) )
  let previousbit ← (( do (undefined_bitvector_at (.site 1181) 1) ) : SailM (BitVec 1) )
  let samplebit ← (( do (undefined_bitvector_at (.site 1182) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let n ← (( do
    if (((_get_CNTHCTL_EL2_Type_EVNTEN w__0) == 1#1) : Bool)
    then
      (do
        let w__1 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
        let n : Int := ((BitVec.toNat (_get_CNTHCTL_EL2_Type_EVNTI w__1)) : Int)
        let w__4 ← (( do
          if ((← do
               (HaveECVExt ())) : Bool)
          then
            (do
              let w__3 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_CNTHCTL_EL2_Type_EVNTIS w__3) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let n : Int :=
          if (w__4 : Bool)
          then (n +i 8)
          else n
        let n : Int := n
        let ecv : Bool := false
        let w__5 ← (( do (HaveECVExt ()) ) : SailM Bool )
        let offset ← (( do
          if (w__5 : Bool)
          then
            (do
              let ecv ← (( do
                if ((← do
                     if ((← do
                          (EL2Enabled ())) : Bool)
                     then
                       (do
                         let w__7 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                         (pure ((((_get_CNTHCTL_EL2_Type_ECV w__7) == 1#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__9 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure ((((_get_SCR_EL3_Type_ECVEn w__9) == 1#1) : Bool))))
                else (pure false) ) : SailM Bool )
              if (ecv : Bool)
              then
                (do
                  readReg CNTPOFF_EL2)
              else (pure ((Zeros (n := 64)))))
          else (pure (offset)) ) : SailM (BitVec 64) )
        ArmFull.assert ((0 ≤b n) && (n <b 64)) "sail-inputs/03-v8_base.sail:18373.46-18373.47"
        let samplebit : (BitVec 1) :=
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (current_physical_count - offset)
              (Sail.Int.toNatChecked (n)))]))
        let previousbit : (BitVec 1) :=
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (prev_physical_count - offset)
              (Sail.Int.toNatChecked (n)))]))
        let w__12 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
        if (((_get_CNTHCTL_EL2_Type_EVNTDIR w__12) == 0#1) : Bool)
        then
          (do
            if (((previousbit == 0#1) && (samplebit == 1#1)) : Bool)
            then
              (do
                (SetEventRegister ()))
            else (pure (())))
        else
          (do
            if (((previousbit == 1#1) && (samplebit == 0#1)) : Bool)
            then
              (do
                (SetEventRegister ()))
            else (pure (())))
        (pure (n)))
    else (pure (n)) ) : SailM Int )
  let n : Int := n
  (pure (()))


def TestEventCNTV (prev_physical_count : (BitVec 64)) (current_physical_count : (BitVec 64)) : SailM Unit := do
  let n ← (( do (undefined_int_at (.site 1184) ()) ) : SailM Int )
  let offset ← (( do (undefined_bitvector_at (.site 1185) 64) ) : SailM (BitVec 64) )
  let previousbit ← (( do (undefined_bitvector_at (.site 1186) 1) ) : SailM (BitVec 1) )
  let samplebit ← (( do (undefined_bitvector_at (.site 1187) 1) ) : SailM (BitVec 1) )
  let w__5 ← (( do
    if ((← do
         let w__3 ← (( do
           if ((← do
                (HaveVirtHostExt ())) : Bool)
           then
             (do
               let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               (pure (((((_get_HCR_EL2_Type_E2H w__1) +++ (_get_HCR_EL2_Type_TGE w__2)) == 0b11#2) : Bool))))
           else (pure false) ) : SailM Bool )
         (pure (((! w__3) : Bool)))) : Bool)
    then
      (do
        let w__4 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTKCTL_EL1_Type_EVNTEN w__4) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let n ← (( do
    if (w__5 : Bool)
    then
      (do
        let w__6 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
        let n : Int := ((BitVec.toNat (_get_CNTKCTL_EL1_Type_EVNTI w__6)) : Int)
        let w__9 ← (( do
          if ((← do
               (HaveECVExt ())) : Bool)
          then
            (do
              let w__8 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
              (pure ((((_get_CNTKCTL_EL1_Type_EVNTIS w__8) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let n : Int :=
          if (w__9 : Bool)
          then (n +i 8)
          else n
        let n : Int := n
        let w__15 ← (( do
          if ((← do
               (HaveEL EL2)) : Bool)
          then
            (do
              if ((← do
                   let w__11 ← (( do (EL2Enabled ()) ) : SailM Bool )
                   (pure (((! w__11) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__12 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure (((((_get_HCR_EL2_Type_E2H w__12) +++ (_get_HCR_EL2_Type_TGE w__13)) != 0b11#2) : Bool)))))
          else (pure false) ) : SailM Bool )
        let offset ← (( do
          if (w__15 : Bool)
          then
            (do
              readReg CNTVOFF_EL2)
          else
            (let offset : (BitVec 64) := (Zeros (n := 64))
            (pure (offset))) ) : SailM (BitVec 64) )
        ArmFull.assert ((0 ≤b n) && (n <b 64)) "sail-inputs/03-v8_base.sail:18424.46-18424.47"
        let samplebit : (BitVec 1) :=
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (current_physical_count - offset)
              (Sail.Int.toNatChecked (n)))]))
        let previousbit : (BitVec 1) :=
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (prev_physical_count - offset)
              (Sail.Int.toNatChecked (n)))]))
        let w__17 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
        if (((_get_CNTKCTL_EL1_Type_EVNTDIR w__17) == 0#1) : Bool)
        then
          (do
            if (((previousbit == 0#1) && (samplebit == 1#1)) : Bool)
            then
              (do
                (SetEventRegister ()))
            else (pure (())))
        else
          (do
            if (((previousbit == 1#1) && (samplebit == 0#1)) : Bool)
            then
              (do
                (SetEventRegister ()))
            else (pure (())))
        (pure (n)))
    else (pure (n)) ) : SailM Int )
  let n : Int := n
  (pure (()))


def IsTCR2EL2Enabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveFeatTCR2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__3 ← (( do
        if ((← do
             (HaveEL EL3)) : Bool)
        then
          (do
            let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCR_EL3_Type_TCR2En w__2) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then (pure (false))
      else
        (do
          (EL2Enabled ())))


def SelfHostedExtendedBPWPEnabled (_ : Unit) : SailM Bool := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (NumBreakpointsImplemented ()) ) : SailM Int )
         (pure (((w__0 ≤b 16) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (NumWatchpointsImplemented ()) ) : SailM Int )
        (pure (((w__1 ≤b 16) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (false))
  else
    (do
      let w__9 ← (( do
        if ((← do
             if ((← do
                  (HaveEL EL3)) : Bool)
             then
               (do
                 let w__4 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                 (pure ((((_get_MDCR_EL3_Type_EBWE w__4) == 0#1) : Bool))))
             else (pure false)) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__7 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_MDCR_EL2_Type_EBWE w__7) == 0#1) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__9 : Bool)
      then (pure (false))
      else
        (do
          let w__10 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
          (pure (((_get_MDSCR_EL1_Type_EMBWE w__10) == 1#1)))))


/-- Type quantifiers: k_isbreakpnt : Bool -/
def CheckValidStateMatch (ssc_in : (BitVec 2)) (ssce_in : (BitVec 1)) (hmc_in : (BitVec 1)) (pxc_in : (BitVec 2)) (isbreakpnt : Bool) : SailM (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) := SailME.run do
  let w__0 ← (( do (HaveRME ()) ) : SailME
    (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
  if ((! w__0) : Bool)
  then
    (do
      ArmFull.assert (ssce_in == 0#1) "sail-inputs/27-armcert_c27b.sail:442.29-442.30")
  else (pure (()))
  let reserved : Bool := false
  let ssc : (BitVec 2) := ssc_in
  let ssce : (BitVec 1) := ssce_in
  let hmc : (BitVec 1) := hmc_in
  let pxc : (BitVec 2) := pxc_in
  let reserved ← (( do
    match (BitVec.setWidth 6 (((hmc +++ ssce) +++ ssc) +++ pxc)) with
    | 0b001110 => (pure (true))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 5 3)) == (0b001#3 : (BitVec 3))) : Bool)
        then
          (do
            let w__1 ← (( do (HaveSecureState ()) ) : SailME
              (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
            let reserved := ((! w__1) : Bool)
            (pure (reserved)))
        else
          (let reserved : Bool :=
            if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 5 2)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
            then true
            else
              (match b__0 with
              | 0b100110 => true
              | b__0 =>
                (if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 5 3)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
                then true
                else
                  (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (1#1 : (BitVec 1))) : Bool)
                  then
                    ((ssc != 0b01#2) || (((hmc +++ pxc) == 0b000#3) || ((hmc +++ pxc) == 0b110#3)))
                  else false)))
          (pure (reserved)))) ) : SailME
    (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
  let w__5 ← (( do
    (pure ((← do
          (pure ((← do
                if (((! isbreakpnt) : Bool) : Bool)
                then (pure true)
                else
                  (do
                    let w__2 ← (( do (HaveAArch32EL EL1) ) : SailME
                      (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
                    (pure (((! w__2) : Bool))))) && (((hmc +++ pxc) == 0b000#3) : Bool)))) && ((ssc != 0b11#2) : Bool)))
    ) : SailME (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
  let reserved : Bool :=
    if (w__5 : Bool)
    then true
    else reserved
  let w__9 ← (( do
    (pure ((← do
          if ((← do
               let w__6 ← (( do (HaveEL EL3) ) : SailME
                 (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
               (pure (((! w__6) : Bool)))) : Bool)
          then
            (do
              let w__7 ← (( do (HaveEL EL2) ) : SailME
                (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
              (pure (((! w__7) : Bool))))
          else (pure false)) && (((hmc != 0#1) || (ssc != 0b00#2)) : Bool))) ) : SailME
    (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
  let reserved : Bool :=
    if (w__9 : Bool)
    then true
    else reserved
  let w__12 ← (( do
    (pure ((← do
          (pure ((← do
                let w__10 ← (( do (HaveEL EL3) ) : SailME
                  (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
                (pure (((! w__10) : Bool)))) && (((ssc == 0b01#2) || (ssc == 0b10#2)) : Bool)))) && ((((hmc +++ ssc) +++ pxc) != 0b10100#5) : Bool)))
    ) : SailME (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
  let reserved : Bool :=
    if (w__12 : Bool)
    then true
    else reserved
  let w__16 ← (( do
    (pure ((← do
          if ((← do
               let w__13 ← (( do (HaveEL EL3) ) : SailME
                 (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
               (pure (((! w__13) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              let w__14 ← (( do (HaveAArch64 ()) ) : SailME
                (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
              (pure (((! w__14) : Bool))))) && ((((hmc +++ ssc) +++ pxc) == 0b11000#5) : Bool))) ) :
    SailME (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
  let reserved : Bool :=
    if (w__16 : Bool)
    then true
    else reserved
  let w__18 ← (( do
    (pure ((← do
          let w__17 ← (( do (HaveEL EL2) ) : SailME
            (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
          (pure (((! w__17) : Bool)))) && ((((hmc +++ ssc) +++ pxc) == 0b11100#5) : Bool))) ) :
    SailME (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
  let reserved : Bool :=
    if (w__18 : Bool)
    then true
    else reserved
  let w__20 ← (( do
    (pure ((← do
          let w__19 ← (( do (HaveSecureEL2Ext ()) ) : SailME
            (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
          (pure (((! w__19) : Bool)))) && (match (BitVec.setWidth 5 ((hmc +++ ssc) +++ pxc)) with
        | 0b01100 => true
        | 0b10100 => true
        | b__4 =>
          (if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__4 3 2)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   b__4 0 0)) == (1#1 : (BitVec 1)))) : Bool)
          then true
          else false) : Bool))) ) : SailME
    (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Bool )
  let reserved : Bool :=
    if (w__20 : Bool)
    then true
    else reserved
  let (hmc, pxc, ssc, ssce) ← (( do
    if (reserved : Bool)
    then
      (do
        let c ← (( do (undefined_Constraint (← occLabel 1380) ()) ) : SailME
          (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) Constraint )
        let w__21 ← (( do (C27bConstrainControl isbreakpnt) ) : SailME
          (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2))
          (Constraint × (BitVec 6)) )
        let (tup__0, tup__1) := (w__21 : (Constraint × (BitVec 6)))
        let c : Constraint := tup__0
        let hmc : (BitVec 1) := (Sail.BitVec.extractLsb tup__1 5 5)
        let ssc : (BitVec 2) := (Sail.BitVec.extractLsb tup__1 4 3)
        let ssce : (BitVec 1) := (Sail.BitVec.extractLsb tup__1 2 2)
        let pxc : (BitVec 2) := (Sail.BitVec.extractLsb tup__1 1 0)
        ArmFull.assert ((BEq.beq c Constraint_DISABLED) || (BEq.beq c Constraint_UNKNOWN)) "sail-inputs/27-armcert_c27b.sail:498.65-498.66"
        if ((BEq.beq c Constraint_DISABLED) : Bool)
        then
          (do
            let w__22 ← (( do (__UNKNOWN_bits 2) ) : SailME
              (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) (BitVec 2) )
            let w__23 ← (( do (__UNKNOWN_bit ()) ) : SailME
              (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) (BitVec 1) )
            let w__24 ← (( do (__UNKNOWN_bit ()) ) : SailME
              (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) (BitVec 1) )
            let w__25 ← (( do (__UNKNOWN_bits 2) ) : SailME
              (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) (BitVec 2) )
            SailME.throw ((c, w__22, w__23, w__24, w__25) : (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2))))
        else (pure (()))
        (pure ((hmc, pxc, ssc, ssce))))
    else (pure ((hmc, pxc, ssc, ssce))) ) : SailME
    (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2))
    ((BitVec 1) × (BitVec 2) × (BitVec 2) × (BitVec 1)) )
  (pure ((Constraint_NONE, ssc, ssce, hmc, pxc)))


def AArch64_S1Enabled (regime : Regime) (acctype : AccessType) : SailM Bool := do
  match regime with
  | .Regime_EL3 =>
    (do
      let w__0 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL3_Type_M w__0) == 1#1))))
  | .Regime_EL2 =>
    (do
      let w__1 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL2_Type_M w__1) == 1#1))))
  | .Regime_EL20 =>
    (do
      let w__2 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL2_Type_M w__2) == 1#1))))
  | .Regime_EL10 =>
    (do
      if ((← do
           if ((← do
                let w__3 ← (( do (EL2Enabled ()) ) : SailM Bool )
                (pure (((! w__3) : Bool)))) : Bool)
           then (pure true)
           else
             (do
               let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               (pure (((((_get_HCR_EL2_Type_DC w__4) +++ (_get_HCR_EL2_Type_TGE w__5)) == 0b00#2) : Bool))))) : Bool)
      then
        (do
          let w__7 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
          (pure ((((_get_SCTLR_EL1_Type_M w__7) == 1#1) : Bool))))
      else (pure false))
  | _ =>
    (do
      (undefined_bool_at (← occLabel 1465) ()))


def VMID_read (_ : Unit) : SailM (BitVec 16) := do
  let w__0 ← (( do (EL2Enabled ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          let w__4 ← (( do
            if ((← do
                 (Have16bitVMID ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_VTCR_EL2_Type_VS w__3) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let w__5 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
              (pure ((_get_VTTBR_EL2_Type_VMID w__5))))
          else
            (do
              let w__6 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
              (pure ((Sail.BitVec.zeroExtend
                  (Sail.BitVec.extractLsb (_get_VTTBR_EL2_Type_VMID w__6) 7 0) 16)))))
      else
        (do
          let w__8 ← (( do readReg VTTBR ) : SailM (BitVec 64) )
          (pure ((Sail.BitVec.zeroExtend (_get_VTTBR_Type_VMID w__8) 16)))))
  else
    (do
      let w__12 ← (( do
        if ((← do
             (HaveEL EL2)) : Bool)
        then
          (do
            (HaveSecureEL2Ext ()))
        else (pure false) ) : SailM Bool )
      let w__13 : (BitVec 16) :=
        if (w__12 : Bool)
        then (Zeros (n := 16))
        else VMID_NONE
      (pure (w__13)))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_S1ApplyTablePerms (permissions_in : Permissions) (descriptor : (BitVec k_N)) (regime : Regime) (walkparams : S1TTWParams) : SailM Permissions := do
  let permissions : Permissions := permissions_in
  let ap_table ← (( do (undefined_bitvector_at (← occLabel 1493) 2) ) : SailM (BitVec 2) )
  let pxn_table ← (( do (undefined_bitvector_at (← occLabel 1494) 1) ) : SailM (BitVec 1) )
  let uxn_table ← (( do (undefined_bitvector_at (← occLabel 1495) 1) ) : SailM (BitVec 1) )
  let xn_table ← (( do (undefined_bitvector_at (← occLabel 1496) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do
    (pure ((← do
          if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
          then
            (do
              (EL2Enabled ()))
          else (pure false)) && ((walkparams.nv1 == 1#1) : Bool))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let (ap_table, pxn_table) ← (( do
        if ((walkparams.d128 == 1#1) : Bool)
        then
          (do
            ArmFull.assert (126 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25591.39-25591.40"
            let ap_table : (BitVec 2) :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 126)])) +++ 0#1)
            let pxn_table : (BitVec 1) :=
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 124)]))
            (pure ((ap_table, pxn_table))))
        else
          (do
            ArmFull.assert (62 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25595.38-25595.39"
            let ap_table : (BitVec 2) :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 62)])) +++ 0#1)
            let pxn_table : (BitVec 1) :=
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 60)]))
            (pure ((ap_table, pxn_table)))) ) : SailM ((BitVec 2) × (BitVec 1)) )
      let permissions : Permissions :=
        { permissions with ap_table := (permissions.ap_table ||| ap_table) }
      let permissions : Permissions :=
        { permissions with pxn_table := (permissions.pxn_table ||| pxn_table) }
      (pure (permissions)))
  else
    (do
      if ((HasUnprivileged regime) : Bool)
      then
        (do
          let (ap_table, pxn_table, uxn_table) ← (( do
            if ((walkparams.d128 == 1#1) : Bool)
            then
              (do
                ArmFull.assert (126 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25603.39-25603.40"
                let ap_table : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 126 125)
                let uxn_table : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 124)]))
                let pxn_table : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 123)]))
                (pure ((ap_table, pxn_table, uxn_table))))
            else
              (do
                ArmFull.assert (62 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25608.38-25608.39"
                let ap_table : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 62 61)
                let uxn_table : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 60)]))
                let pxn_table : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 59)]))
                (pure ((ap_table, pxn_table, uxn_table)))) ) : SailM
            ((BitVec 2) × (BitVec 1) × (BitVec 1)) )
          let permissions : Permissions :=
            { permissions with ap_table := (permissions.ap_table ||| ap_table) }
          let permissions : Permissions :=
            { permissions with uxn_table := (permissions.uxn_table ||| uxn_table) }
          let permissions : Permissions :=
            { permissions with pxn_table := (permissions.pxn_table ||| pxn_table) }
          (pure (permissions)))
      else
        (do
          let (ap_table, xn_table) ← (( do
            if ((walkparams.d128 == 1#1) : Bool)
            then
              (do
                ArmFull.assert (126 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25618.39-25618.40"
                let ap_table : (BitVec 2) :=
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 126)])) +++ 0#1)
                let xn_table : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 124)]))
                (pure ((ap_table, xn_table))))
            else
              (do
                ArmFull.assert (62 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25622.38-25622.39"
                let ap_table : (BitVec 2) :=
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 62)])) +++ 0#1)
                let xn_table : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 60)]))
                (pure ((ap_table, xn_table)))) ) : SailM ((BitVec 2) × (BitVec 1)) )
          let permissions : Permissions :=
            { permissions with ap_table := (permissions.ap_table ||| ap_table) }
          let permissions : Permissions :=
            { permissions with xn_table := (permissions.xn_table ||| xn_table) }
          (pure (permissions))))


end ArmFull.Functions
