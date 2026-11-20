module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0038
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0061
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0120
public import ArmFull.Fn.M0121
public import ArmFull.Fn.M0123 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_N : Nat, List.elem k_N [64, 128] -/
def AArch64_S1OutputMECID (walkparams : S1TTWParams) (regime : Regime) (varange : VARange) (paspace : PASpace) (descriptor : (BitVec k_N)) : SailM (BitVec 16) := do
  ArmFull.assert (((Sail.BitVec.length descriptor) == 64) || ((Sail.BitVec.length descriptor) == 128)) "sail-inputs/03-v8_base.sail:24800.31-24800.32"
  if ((walkparams.emec == 0#1) : Bool)
  then (pure (DEFAULT_MECID))
  else
    (do
      if ((bne paspace PAS_Realm) : Bool)
      then (pure (DEFAULT_MECID))
      else
        (do
          let descriptor_amec ← (( do
            if ((walkparams.d128 == 1#1) : Bool)
            then
              (do
                ArmFull.assert (103 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:24808.35-24808.36"
                (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 103)])))))
            else (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 63)])))) ) :
            SailM (BitVec 1) )
          match regime with
          | .Regime_EL3 =>
            (do
              let w__0 ← (( do readReg MECID_RL_A_EL3 ) : SailM (BitVec 64) )
              (pure ((_get_MECID_RL_A_EL3_Type_MECID w__0))))
          | .Regime_EL2 =>
            (do
              if ((descriptor_amec == 0#1) : Bool)
              then
                (do
                  let w__1 ← (( do readReg MECID_P0_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MECID_P0_EL2_Type_MECID w__1))))
              else
                (do
                  let w__2 ← (( do readReg MECID_A0_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MECID_A0_EL2_Type_MECID w__2)))))
          | .Regime_EL20 =>
            (do
              if ((BEq.beq varange VARange_LOWER) : Bool)
              then
                (do
                  if ((descriptor_amec == 0#1) : Bool)
                  then
                    (do
                      let w__4 ← (( do readReg MECID_P0_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_MECID_P0_EL2_Type_MECID w__4))))
                  else
                    (do
                      let w__5 ← (( do readReg MECID_A0_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_MECID_A0_EL2_Type_MECID w__5)))))
              else
                (do
                  if ((descriptor_amec == 0#1) : Bool)
                  then
                    (do
                      let w__7 ← (( do readReg MECID_P1_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_MECID_P1_EL2_Type_MECID w__7))))
                  else
                    (do
                      let w__8 ← (( do readReg MECID_A1_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_MECID_A1_EL2_Type_MECID w__8))))))
          | .Regime_EL10 =>
            (do
              let w__11 ← (( do readReg VMECID_P_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_VMECID_P_EL2_Type_MECID w__11))))
          | _ =>
            (do
              (undefined_bitvector_at (← occLabel 1470) 16))))


/-- Type quantifiers: level : Int -/
def AArch64_S1SLTTEntryAddress (level : Int) (walkparams : S1TTWParams) (ia : (BitVec 64)) (tablebase : FullAddress) : SailM FullAddress := do
  let iasize : Int := (AArch64_IASize walkparams.txsz)
  let granulebits : Int := (TGxGranuleBits walkparams.tgx)
  let descsizelog2 : Int :=
    if ((walkparams.d128 == 1#1) : Bool)
    then 4
    else 3
  let stride : Int := (granulebits -i descsizelog2)
  let levels : Int := (FINAL_LEVEL -i level)
  let lsb : Int := ((levels *i stride) +i granulebits)
  let msb : Int := (iasize -i 1)
  ArmFull.assert ((0 ≤b lsb) && ((lsb ≤b msb) && (msb <b 64))) "sail-inputs/03-v8_base.sail:25701.61-25701.62"
  ArmFull.assert (56 ≥b (((msb -i lsb) +i 1) +i descsizelog2)) "sail-inputs/03-v8_base.sail:25702.60-25702.61"
  let index : (BitVec 56) :=
    (Sail.BitVec.zeroExtend
      ((Sail.BitVec.extractLsb ia (Sail.Int.toNatChecked (msb)) (Sail.Int.toNatChecked (lsb))) +++ (Zeros
          (n := (Sail.Int.toNatChecked (descsizelog2))))) 56)
  let descaddress ← (( do (undefined_FullAddress (← occLabel 1501) ()) ) : SailM FullAddress )
  let descaddress : FullAddress := { descaddress with address := (tablebase.address ||| index) }
  let descaddress : FullAddress := { descaddress with paspace := tablebase.paspace }
  (pure (descaddress))


def AArch64_S2InconsistentSL (walkparams : S2TTWParams) : SailM Bool := do
  let startlevel ← (( do (AArch64_S2StartLevel walkparams) ) : SailM Int )
  let levels : Int := (FINAL_LEVEL -i startlevel)
  let granulebits : Int := (TGxGranuleBits walkparams.tgx)
  let descsizelog2 : Nat := 3
  let stride : Int := (granulebits -i descsizelog2)
  let sl_min_iasize : Int := (((levels *i stride) +i granulebits) +i 1)
  let sl_max_iasize : Int := ((sl_min_iasize +i (stride -i 1)) +i 4)
  let iasize : Int := (AArch64_IASize walkparams.txsz)
  (pure (((iasize <b sl_min_iasize) || (iasize >b sl_max_iasize))))


/-- Type quantifiers: k_N : Nat, List.elem k_N [64, 128] -/
def AArch64_S2OutputMECID (walkparams : S2TTWParams) (paspace : PASpace) (descriptor : (BitVec k_N)) : SailM (BitVec 16) := do
  ArmFull.assert (((Sail.BitVec.length descriptor) == 64) || ((Sail.BitVec.length descriptor) == 128)) "sail-inputs/03-v8_base.sail:26586.31-26586.32"
  if ((walkparams.emec == 0#1) : Bool)
  then (pure (DEFAULT_MECID))
  else
    (do
      if ((bne paspace PAS_Realm) : Bool)
      then (pure (DEFAULT_MECID))
      else
        (do
          let descriptor_amec ← (( do
            if ((walkparams.d128 == 1#1) : Bool)
            then
              (do
                ArmFull.assert (103 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26594.35-26594.36"
                (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 103)])))))
            else (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 63)])))) ) :
            SailM (BitVec 1) )
          if ((descriptor_amec == 0#1) : Bool)
          then
            (do
              let w__0 ← (( do readReg VMECID_P_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_VMECID_P_EL2_Type_MECID w__0))))
          else
            (do
              let w__1 ← (( do readReg VMECID_A_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_VMECID_A_EL2_Type_MECID w__1))))))


def AArch64_S2SLTTEntryAddress (walkparams : S2TTWParams) (ipa : (BitVec 56)) (tablebase : FullAddress) : SailM FullAddress := do
  let startlevel ← (( do (AArch64_S2StartLevel walkparams) ) : SailM Int )
  let iasize : Int := (AArch64_IASize walkparams.txsz)
  let granulebits : Int := (TGxGranuleBits walkparams.tgx)
  let descsizelog2 : Int :=
    if ((walkparams.d128 == 1#1) : Bool)
    then 4
    else 3
  let stride : Int := (granulebits -i descsizelog2)
  let levels : Int := (FINAL_LEVEL -i startlevel)
  let lsb : Int := ((levels *i stride) +i granulebits)
  let msb : Int := (iasize -i 1)
  ArmFull.assert ((0 ≤b lsb) && ((lsb ≤b msb) && (msb <b 56))) "sail-inputs/03-v8_base.sail:26943.61-26943.62"
  ArmFull.assert (56 ≥b (((msb -i lsb) +i 1) +i descsizelog2)) "sail-inputs/03-v8_base.sail:26944.60-26944.61"
  let index : (BitVec 56) :=
    (Sail.BitVec.zeroExtend
      ((Sail.BitVec.extractLsb ipa (Sail.Int.toNatChecked (msb)) (Sail.Int.toNatChecked (lsb))) +++ (Zeros
          (n := (Sail.Int.toNatChecked (descsizelog2))))) 56)
  let descaddress ← (( do (undefined_FullAddress (← occLabel 1567) ()) ) : SailM FullAddress )
  let descaddress : FullAddress := { descaddress with address := (tablebase.address ||| index) }
  let descaddress : FullAddress := { descaddress with paspace := tablebase.paspace }
  (pure (descaddress))


/-- Type quantifiers: level : Int -/
def AArch64_TTEntryAddress (level : Int) (d128 : (BitVec 1)) (skl : (BitVec 2)) (tgx : TGx) (txsz : (BitVec 6)) (ia : (BitVec 64)) (tablebase : FullAddress) : SailM FullAddress := do
  let iasize : Int := (AArch64_IASize txsz)
  let granulebits : Int := (TGxGranuleBits tgx)
  let descsizelog2 : Int :=
    if ((d128 == 1#1) : Bool)
    then 4
    else 3
  let stride : Int := (granulebits -i descsizelog2)
  let levels : Int := (FINAL_LEVEL -i level)
  let msb ← (( do (undefined_int_at (← occLabel 1571) ()) ) : SailM Int )
  let lsb : Int := ((levels *i stride) +i granulebits)
  let msb : Int :=
    if ((d128 == 1#1) : Bool)
    then ((lsb +i (stride *i (1 +i (BitVec.toNat skl)))) -i 1)
    else ((lsb +i stride) -i 1)
  let msb : Int := msb
  ArmFull.assert ((0 ≤b lsb) && ((lsb ≤b msb) && (msb <b 64))) "sail-inputs/03-v8_base.sail:27001.61-27001.62"
  ArmFull.assert (56 ≥b (((msb -i lsb) +i 1) +i descsizelog2)) "sail-inputs/03-v8_base.sail:27002.60-27002.61"
  let index : (BitVec 56) :=
    (Sail.BitVec.zeroExtend
      ((Sail.BitVec.extractLsb ia (Sail.Int.toNatChecked (msb)) (Sail.Int.toNatChecked (lsb))) +++ (Zeros
          (n := (Sail.Int.toNatChecked (descsizelog2))))) 56)
  let descaddress ← (( do (undefined_FullAddress (← occLabel 1572) ()) ) : SailM FullAddress )
  let descaddress : FullAddress := { descaddress with address := (tablebase.address ||| index) }
  let descaddress : FullAddress := { descaddress with paspace := tablebase.paspace }
  (pure (descaddress))


def AArch64_TTWalkMECID (emec : (BitVec 1)) (regime : Regime) (ss : SecurityState) : SailM (BitVec 16) := do
  if ((emec == 0#1) : Bool)
  then (pure (DEFAULT_MECID))
  else
    (do
      if ((bne ss SS_Realm) : Bool)
      then (pure (DEFAULT_MECID))
      else
        (do
          match regime with
          | .Regime_EL2 =>
            (do
              let w__0 ← (( do readReg MECID_P0_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_MECID_P0_EL2_Type_MECID w__0))))
          | .Regime_EL20 =>
            (do
              let w__1 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
              if (((_get_TCR_EL2_Type_A1 w__1) == 0#1) : Bool)
              then
                (do
                  let w__2 ← (( do readReg MECID_P1_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MECID_P1_EL2_Type_MECID w__2))))
              else
                (do
                  let w__3 ← (( do readReg MECID_P0_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MECID_P0_EL2_Type_MECID w__3)))))
          | .Regime_EL10 =>
            (do
              let w__5 ← (( do readReg VMECID_P_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_VMECID_P_EL2_Type_MECID w__5))))
          | _ =>
            (do
              (Unreachable ())
              (undefined_bitvector_at (← occLabel 1573) 16))))


def PhysMemTagWrite (desc : AddressDescriptor) (accdesc : AccessDescriptor) (data : (BitVec 4)) : SailM PhysMemRetStatus := do
  (undefined_PhysMemRetStatus (← occLabel 1667) ())


def SetPSTATE_SM (value_name : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.SM != value_name) : Bool)
  then
    (do
      (ResetSVEState ())
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with SM := value_name })
  else (pure (()))


def SetPSTATE_ZA (value_name : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.ZA != value_name) : Bool)
  then
    (do
      (ResetSMEState ())
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with ZA := value_name })
  else (pure (()))


/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 -/
def AnyActiveElement (mask : (BitVec k_N)) (esize : Int) : SailM Bool := do
  let w__0 ← (( do (LastActiveElement mask esize) ) : SailM Int )
  (pure ((w__0 ≥b 0)))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPOne (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-inputs/03-v8_base.sail:29928.38-29928.39"
  let E : Nat :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F : Int := (N -i (E +i 1))
  let exp : (BitVec (1 + ((Sail.Int.toNatChecked E) - 1))) :=
    (Sail.BitVec.castWidth (0#1 +++ (Ones (n := (Sail.Int.toNatChecked ((E -i 1)))))))
  let frac : (BitVec (Sail.Int.toNatChecked (F : Int))) :=
    (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (F)))))
  (pure ((Sail.BitVec.castWidth ((sign +++ exp) +++ frac))))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPPointFive (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-inputs/03-v8_base.sail:29939.38-29939.39"
  let E : Nat :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F : Int := (N -i (E +i 1))
  let exp : (BitVec (1 + ((Sail.Int.toNatChecked E) - 2) + 1)) :=
    (Sail.BitVec.castWidth ((0#1 +++ (Ones (n := (Sail.Int.toNatChecked ((E -i 2)))))) +++ 0#1))
  let frac : (BitVec (Sail.Int.toNatChecked (F : Int))) :=
    (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (F)))))
  (pure ((Sail.BitVec.castWidth ((sign +++ exp) +++ frac))))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPExpA (op : (BitVec k_N)) : SailM (BitVec k_N) := do
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "sail-inputs/03-v8_base.sail:30734.41-30734.42"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1742)
      (Sail.BitVec.length op))) ) : SailM (BitVec k_N) )
  let idx : Int :=
    if (((Sail.BitVec.length result) == 16) : Bool)
    then (BitVec.toNat (Sail.BitVec.extractLsb op 4 0))
    else (BitVec.toNat (Sail.BitVec.extractLsb op 5 0))
  let coeff ← (( do
    ((Sail.BitVec.castWidth ) <$> (FPExpCoefficient_read idx (Sail.BitVec.length result))) ) : SailM
    (BitVec k_N) )
  let result : (BitVec k_N) :=
    if (((Sail.BitVec.length result) == 16) : Bool)
    then
      (Sail.BitVec.updateSubrange result 15 0
        ((0#1 +++ (Sail.BitVec.extractLsb op 9 5)) +++ (Sail.BitVec.extractLsb coeff 9 0)))
    else
      (if (((Sail.BitVec.length result) == 32) : Bool)
      then
        (Sail.BitVec.updateSubrange result 31 0
          ((0#1 +++ (Sail.BitVec.extractLsb op 13 6)) +++ (Sail.BitVec.extractLsb coeff 22 0)))
      else
        (Sail.BitVec.updateSubrange result 63 0
          ((0#1 +++ (Sail.BitVec.extractLsb op 16 6)) +++ (Sail.BitVec.extractLsb coeff 51 0))))
  (pure ((Sail.BitVec.castWidth result)))


/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 -/
def PredTest (mask : (BitVec k_N)) (result : (BitVec k_N)) (esize : Int) : SailM (BitVec 4) := do
  let n ← (( do (FirstActive mask result esize) ) : SailM (BitVec 1) )
  let z ← (( do (NoneActive mask result esize) ) : SailM (BitVec 1) )
  let w__0 ← (( do (LastActive mask result esize) ) : SailM (BitVec 1) )
  let c : (BitVec 1) := (Complement.complement w__0)
  let v : (BitVec 1) := 0#1
  (pure ((((n +++ z) +++ c) +++ v)))


/-- Type quantifiers: M : Nat, k_immediate : Bool, M ≥ 0 -/
def DecodeBitMasks (immN : (BitVec 1)) (imms : (BitVec 6)) (immr : (BitVec 6)) (immediate : Bool) (M : Nat) : SailM ((BitVec M) × (BitVec M)) := do
  let len : Int := (HighestSetBit (immN +++ (Complement.complement imms)))
  if ((len <b 1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  ArmFull.assert (M ≥b (Int.shiftl 1 (Sail.Int.toNatChecked (len)))) "sail-inputs/03-v8_base.sail:30910.26-30910.27"
  ArmFull.assert (6 ≥b len) "sail-inputs/03-v8_base.sail:30911.32-30911.33"
  let levels : (BitVec 6) := (Sail.BitVec.zeroExtend (Ones (n := (Sail.Int.toNatChecked (len)))) 6)
  if ((immediate && ((imms &&& levels) == levels)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (imms &&& levels))
  let r : Int := (BitVec.toNat (immr &&& levels))
  let diff : Int := (s -i r)
  let esize : Int := (Int.shiftl 1 (Sail.Int.toNatChecked (len)))
  let d : Int := (BitVec.toNat (integer_subrange diff (len -i 1) 0))
  ArmFull.assert (esize ≥b (s +i 1)) "sail-inputs/03-v8_base.sail:30921.39-30921.40"
  let welem : (BitVec (Sail.Int.toNatChecked (esize : Int))) :=
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend (Ones (n := (Sail.Int.toNatChecked ((s +i 1)))))
      (Sail.Int.toNatChecked (esize))))
  ArmFull.assert (esize ≥b (d +i 1)) "sail-inputs/03-v8_base.sail:30923.39-30923.40"
  let telem : (BitVec (Sail.Int.toNatChecked (esize : Int))) :=
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend (Ones (n := (Sail.Int.toNatChecked ((d +i 1)))))
      (Sail.Int.toNatChecked (esize))))
  ArmFull.assert ((esize *i (Int.ediv M esize)) == M) "sail-inputs/03-v8_base.sail:30925.53-30925.54"
  let wmask : (BitVec M) :=
    (Sail.BitVec.castWidth (BitVec.replicateBits (ROR welem (Sail.Int.toNatChecked (r)))
      (Sail.Int.toNatChecked ((Int.ediv M (Sail.Int.toNatChecked (esize)))))))
  let tmask : (BitVec M) :=
    (Sail.BitVec.castWidth (BitVec.replicateBits telem
      (Sail.Int.toNatChecked ((Int.ediv M (Sail.Int.toNatChecked (esize)))))))
  (pure ((wmask, tmask)))


/-- Type quantifiers: val_name : Int -/
def IsEven (val_name : Int) : Bool :=
  ((fmod_int val_name 2) == 0)


def HaveSVEFP32MatMulExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_F32MM)


def HaveSVEFP64MatMulExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_F64MM)


def HaveSVE2 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SVE2)


def HaveSVE2AES (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SVE_AES)


def HaveSVE2PMULL128 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SVE_PMULL128)


def HaveSVE2SHA3 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SVE_SHA3)


def HaveSVE2SM4 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SVE_SM4)


def HaveSVE2BitPerm (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SVE_BitPerm)


def HaveSVE2p1 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SVE2p1)


def HaveSVEB16B16 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SVE_B16B16)


def HaveSMEF64F64 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SME_F64F64)


def HaveSMEI16I64 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SME_I16I64)


def HaveSME2 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SME2)


def HaveSME2p1 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SME2p1)


def HaveSMEB16B16 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SVE_B16B16)


def HaveSMEF16F16 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SME_F16F16)


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32] -/
def BFUnpack (fpval : (BitVec k_N)) : SailM (FPType × (BitVec 1) × real) := do
  ArmFull.assert (((Sail.BitVec.length fpval) == 16) || ((Sail.BitVec.length fpval) == 32)) "sail-inputs/03-v8_base.sail:32066.30-32066.31"
  let sign ← (( do (undefined_bitvector_at (← occLabel 1767) 1) ) : SailM (BitVec 1) )
  let exp ← (( do (undefined_bitvector_at (← occLabel 1768) 8) ) : SailM (BitVec 8) )
  let frac ← (( do (undefined_bitvector_at (← occLabel 1769) 23) ) : SailM (BitVec 23) )
  let (exp, frac, sign) : ((BitVec 8) × (BitVec 23) × (BitVec 1)) :=
    if (((Sail.BitVec.length fpval) == 16) : Bool)
    then
      (let sign : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access fpval 15)]))
      let exp : (BitVec 8) := (Sail.BitVec.extractLsb fpval 14 7)
      let frac : (BitVec 23) := ((Sail.BitVec.extractLsb fpval 6 0) +++ (Zeros (n := 16)))
      (exp, frac, sign))
    else
      (let sign : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access fpval 31)]))
      let exp : (BitVec 8) := (Sail.BitVec.extractLsb fpval 30 23)
      let frac : (BitVec 23) := (Sail.BitVec.extractLsb fpval 22 0)
      (exp, frac, sign))
  let fptype ← (( do (undefined_FPType (← occLabel 1770) ()) ) : SailM FPType )
  let value_name ← (( do (undefined_real_at (← occLabel 1771) ()) ) : SailM real )
  let (fptype, value_name) : (FPType × real) :=
    if ((IsZero exp) : Bool)
    then
      (let fptype : FPType := FPType_Zero
      let value_name : real := (0)
      (fptype, value_name))
    else
      (let (fptype, value_name) : (FPType × real) :=
        if ((IsOnes exp) : Bool)
        then
          (let (fptype, value_name) : (FPType × real) :=
            if ((IsZero frac) : Bool)
            then
              (let fptype : FPType := FPType_Infinity
              let value_name : real := (real_power (2) 1000000)
              (fptype, value_name))
            else
              (let fptype : FPType := FPType_QNaN
              let value_name : real := (0)
              (fptype, value_name))
          (fptype, value_name))
        else
          (let fptype : FPType := FPType_Nonzero
          let value_name : real :=
            (mult_real (real_power (2) ((BitVec.toNat exp) -i 127))
              (add_real (1) (mult_real (to_real (BitVec.toNat frac)) (real_power (2) (Neg.neg 23)))))
          (fptype, value_name))
      (fptype, value_name))
  let value_name : real :=
    if ((sign == 1#1) : Bool)
    then (neg_real value_name)
    else value_name
  let value_name := value_name
  (pure ((fptype, sign, value_name)))


/-- Type quantifiers: N : Nat, N = 16 -/
def BFInfinity (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert (N == 16) "sail-inputs/03-v8_base.sail:32484.18-32484.19"
  let E : Nat := 8
  let F : Int := (N -i (E +i 1))
  (pure ((Sail.BitVec.castWidth ((sign +++ (Ones (n := E))) +++ (Zeros
        (n := (Sail.Int.toNatChecked (F))))))))


/-- Type quantifiers: k_cold : Bool -/
def __Reset (cold : Bool) : SailM Unit := do
  writeReg __last_cycle_count 0
  writeReg __last_branch_valid false
  writeReg sp_rel_access_pc (Ones (n := 64))
  writeReg __cycle_count 0


/-- Type quantifiers: k_conditional : Bool, k_taken : Bool -/
def SPESampleAddOpOther (conditional : Bool) (taken : Bool) : SailM Unit := do
  let w__0 ← (( do readReg SPESampleEvents ) : SailM (BitVec 64) )
  writeReg SPESampleEvents (BitVec.update w__0 6
    (Bit
      (if ((conditional && (! taken)) : Bool)
      then 1#1
      else 0#1)))
  (SPESampleAddOpOther__1 conditional)


/-- Type quantifiers: k_N : Nat, List.elem k_N [8, 16, 32, 64] -/
def SPEAddPacketToRecord (header_hi : (BitVec 2)) (header_lo : (BitVec 4)) (payload : (BitVec k_N)) : SailM Unit := do
  ArmFull.assert ((Nat.mod (Sail.BitVec.length payload) 8) == 0) "sail-inputs/03-v8_base.sail:35125.26-35125.27"
  let sz ← (( do (undefined_bitvector_at (← occLabel 2436) 2) ) : SailM (BitVec 2) )
  let sz ← (( do
    match (Sail.BitVec.length payload) with
    | 8 => (pure (0b00#2))
    | 16 => (pure (0b01#2))
    | 32 => (pure (0b10#2))
    | 64 => (pure (0b11#2))
    | _ =>
      (do
        (Unreachable ())
        (pure (sz))) ) : SailM (BitVec 2) )
  let header : (BitVec 8) := ((header_hi +++ sz) +++ header_lo)
  (SPEAddByteToRecord header)
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat :=
    (Sail.Int.toNatChecked (((Int.ediv (Sail.BitVec.length payload) 8) -i 1)))
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (SPEAddByteToRecord
          (Sail.BitVec.castWidth (Sail.BitVec.extractLsb payload
            (Sail.Int.toNatChecked (((i *i 8) +i 7))) (Sail.Int.toNatChecked ((i *i 8))))))
    (pure loop_vars))


def AArch64_TLBI_ALL (security : SecurityState) (regime : Regime) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL2) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:35925.46-35925.47"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2461) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_ALL }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch64_TLBI_VMALL (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:35943.65-35943.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2462) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VMALL }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch64_TLBI_VMALLS12 (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL2) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:35962.46-35962.47"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2463) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_VMALLS12 }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with attr := attr }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


def AArch64_TLBI_ASID (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:35981.65-35981.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2464) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_ASID }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := TLBILevel_Any }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := (Sail.BitVec.extractLsb Xt 63 48) }
  (TLBI r shareability)
  let _ : Unit :=
    if ((bne shareability Shareability_NSH) : Bool)
    then (Broadcast shareability r)
    else ()
  (pure (()))


end ArmFull.Functions
