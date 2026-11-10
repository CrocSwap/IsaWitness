import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0019
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0038
import ArmFull.Fn.M0044
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0113
import ArmFull.Fn.M0120
import ArmFull.Fn.M0121

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

def AArch64_S1DisabledOutputMECID (walkparams : S1TTWParams) (regime : Regime) (paspace : PASpace) : SailM (BitVec 16) := do
  if ((walkparams.emec == 0#1) : Bool)
  then (pure (DEFAULT_MECID))
  else
    (do
      if ((! ((BEq.beq regime Regime_EL2) || ((BEq.beq regime Regime_EL20) || (BEq.beq regime
                 Regime_EL10)))) : Bool)
      then (pure (DEFAULT_MECID))
      else
        (do
          if ((bne paspace PAS_Realm) : Bool)
          then (pure (DEFAULT_MECID))
          else
            (do
              if ((BEq.beq regime Regime_EL10) : Bool)
              then
                (do
                  let w__0 ← (( do readReg VMECID_P_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_VMECID_P_EL2_Type_MECID w__0))))
              else
                (do
                  let w__1 ← (( do readReg MECID_P0_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MECID_P0_EL2_Type_MECID w__1)))))))


/-- Type quantifiers: k_N : Nat, List.elem k_N [64, 128] -/
def AArch64_S1OutputMECID (walkparams : S1TTWParams) (regime : Regime) (varange : VARange) (paspace : PASpace) (descriptor : (BitVec k_N)) : SailM (BitVec 16) := do
  ArmFull.assert (((Sail.BitVec.length descriptor) == 64) || ((Sail.BitVec.length descriptor) == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:24790.31-24790.32"
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
                ArmFull.assert (103 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:24798.35-24798.36"
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
  ArmFull.assert ((0 ≤b lsb) && ((lsb ≤b msb) && (msb <b 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25691.61-25691.62"
  ArmFull.assert (56 ≥b (((msb -i lsb) +i 1) +i descsizelog2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25692.60-25692.61"
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
  ArmFull.assert (((Sail.BitVec.length descriptor) == 64) || ((Sail.BitVec.length descriptor) == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26576.31-26576.32"
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
                ArmFull.assert (103 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26584.35-26584.36"
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
  ArmFull.assert ((0 ≤b lsb) && ((lsb ≤b msb) && (msb <b 56))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26933.61-26933.62"
  ArmFull.assert (56 ≥b (((msb -i lsb) +i 1) +i descsizelog2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26934.60-26934.61"
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
  ArmFull.assert ((0 ≤b lsb) && ((lsb ≤b msb) && (msb <b 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26991.61-26991.62"
  ArmFull.assert (56 ≥b (((msb -i lsb) +i 1) +i descsizelog2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26992.60-26992.61"
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
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:29918.38-29918.39"
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
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:29929.38-29929.39"
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
          op) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30724.41-30724.42"
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
  ArmFull.assert (M ≥b (Int.shiftl 1 (Sail.Int.toNatChecked (len)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30900.26-30900.27"
  ArmFull.assert (6 ≥b len) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30901.32-30901.33"
  let levels : (BitVec 6) := (Sail.BitVec.zeroExtend (Ones (n := (Sail.Int.toNatChecked (len)))) 6)
  if ((immediate && ((imms &&& levels) == levels)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (imms &&& levels))
  let r : Int := (BitVec.toNat (immr &&& levels))
  let diff : Int := (s -i r)
  let esize : Int := (Int.shiftl 1 (Sail.Int.toNatChecked (len)))
  let d : Int := (BitVec.toNat (integer_subrange diff (len -i 1) 0))
  ArmFull.assert (esize ≥b (s +i 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30911.39-30911.40"
  let welem : (BitVec (Sail.Int.toNatChecked (esize : Int))) :=
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend (Ones (n := (Sail.Int.toNatChecked ((s +i 1)))))
      (Sail.Int.toNatChecked (esize))))
  ArmFull.assert (esize ≥b (d +i 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30913.39-30913.40"
  let telem : (BitVec (Sail.Int.toNatChecked (esize : Int))) :=
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend (Ones (n := (Sail.Int.toNatChecked ((d +i 1)))))
      (Sail.Int.toNatChecked (esize))))
  ArmFull.assert ((esize *i (Int.ediv M esize)) == M) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30915.53-30915.54"
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
  ArmFull.assert (((Sail.BitVec.length fpval) == 16) || ((Sail.BitVec.length fpval) == 32)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:32056.30-32056.31"
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
  ArmFull.assert (N == 16) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:32474.18-32474.19"
  let E : Nat := 8
  let F : Int := (N -i (E +i 1))
  (pure ((Sail.BitVec.castWidth ((sign +++ (Ones (n := E))) +++ (Zeros
        (n := (Sail.Int.toNatChecked (F))))))))


def MPAM1_EL1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM1_EL1_Type := value_name
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__0 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
      (MPAM3_EL3_write (Mk_MPAM3_EL3_Type (set_slice 1 w__0 63 (BitVec.slice r 63 1)))))
  else
    (do
      let w__1 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
      writeReg MPAM2_EL2 (BitVec.update w__1 63 (Bit (BitVec.slice r 63 1))))
  writeReg _MPAM1_EL1 r


/-- Type quantifiers: k_cold : Bool -/
def AArch64_AutoGen_ArchitectureReset__seg0 (cold : Bool) : SailM Bool := do
  let w__0 ← (( do readReg ID_MMFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR2_EL1 (Sail.BitVec.updateSubrange w__0 63 32 0b00000000000000000000000000000000#32)
  let w__1 ← (( do readReg ID_MMFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR2_EL1 (Sail.BitVec.updateSubrange w__1 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__2 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__2 63 32 0b00000000000000000000000000000000#32)
  let w__3 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__3 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__4 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__4 47 44 0b0000#4)
  let w__5 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (Sail.BitVec.updateSubrange w__5 63 45 0b0000000000000000000#19)
  let w__6 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (Sail.BitVec.updateSubrange w__6 43 42 0b00#2)
  let w__7 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (BitVec.update w__7 39 (Bit 0#1))
  let w__8 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (BitVec.update w__8 31 (Bit 1#1))
  let w__9 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (Sail.BitVec.updateSubrange w__9 24 23 0b00#2)
  let w__10 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (BitVec.update w__10 20 (Bit 0#1))
  let w__11 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__11 63 63 0#1)
  let w__12 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__12 62 62 0#1)
  let w__13 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__13 61 61 0#1)
  let w__14 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__14 60 60 0#1)
  let w__15 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__15 59 59 0#1)
  let w__16 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__16 58 58 0#1)
  let w__17 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__17 57 57 0#1)
  let w__18 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__18 56 49 0b00000000#8)
  let w__19 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__19 48 48 0#1)
  let w__20 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__20 47 47 0#1)
  let w__21 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__21 46 46 0#1)
  let w__22 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__22 45 45 0#1)
  let w__23 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__23 44 44 0#1)
  let w__24 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__24 43 43 0#1)
  let w__25 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (BitVec.update w__25 42 (Bit 0#1))
  let w__26 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__26 41 41 0#1)
  let w__27 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__27 40 40 0#1)
  let w__28 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__28 39 38 0b00#2)
  let w__29 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__29 37 37 0#1)
  let w__30 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__30 36 36 0#1)
  let w__31 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__31 35 35 0#1)
  let w__32 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__32 34 34 0#1)
  let w__33 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__33 33 33 0#1)
  let w__34 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__34 32 32 0#1)
  let w__35 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__35 31 31 0#1)
  let w__36 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__36 30 30 0#1)
  let w__37 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__37 29 29 0#1)
  let w__38 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__38 28 28 0#1)
  let w__39 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__39 27 27 0#1)
  let w__40 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__40 26 26 0#1)
  let w__41 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__41 25 25 0#1)
  let w__42 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__42 24 24 0#1)
  let w__43 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__43 23 23 0#1)
  let w__44 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__44 22 22 0#1)
  let w__45 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__45 21 20 0b00#2)
  let w__46 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__46 19 19 0#1)
  let w__47 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__47 18 18 0#1)
  let w__48 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__48 17 17 0#1)
  let w__49 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__49 16 16 0#1)
  let w__50 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__50 15 15 0#1)
  let w__51 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__51 14 14 0#1)
  let w__52 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__52 13 13 0#1)
  let w__53 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__53 12 12 0#1)
  let w__54 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__54 11 11 0#1)
  let w__55 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__55 10 10 0#1)
  let w__56 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__56 9 9 0#1)
  let w__57 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (BitVec.update w__57 8 (Bit 0#1))
  let w__58 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__58 7 7 0#1)
  let w__59 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__59 6 6 0#1)
  let w__60 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__60 5 5 0#1)
  let w__61 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__61 4 4 0#1)
  let w__62 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__62 3 3 0#1)
  let w__63 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__63 2 2 0#1)
  let w__64 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__64 1 1 0#1)
  let w__65 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__65 0 0 0#1)
  let w__66 ← (( do readReg ICV_NMIAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_NMIAR1_EL1 (Sail.BitVec.updateSubrange w__66 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__67 ← (( do readReg SPSR_abt ) : SailM (BitVec 64) )
  writeReg SPSR_abt (Sail.BitVec.updateSubrange w__67 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__68 ← (( do readReg SPSR_abt ) : SailM (BitVec 64) )
  writeReg SPSR_abt (Sail.BitVec.updateSubrange w__68 63 32 0b00000000000000000000000000000000#32)
  let w__69 ← (( do readReg MDCCINT_EL1 ) : SailM (BitVec 64) )
  writeReg MDCCINT_EL1 (Sail.BitVec.updateSubrange w__69 63 31
    0b000000000000000000000000000000000#33)
  let w__70 ← (( do readReg MDCCINT_EL1 ) : SailM (BitVec 64) )
  writeReg MDCCINT_EL1 (Sail.BitVec.updateSubrange w__70 30 30 0#1)
  let w__71 ← (( do readReg MDCCINT_EL1 ) : SailM (BitVec 64) )
  writeReg MDCCINT_EL1 (Sail.BitVec.updateSubrange w__71 29 29 0#1)
  let w__72 ← (( do readReg MDCCINT_EL1 ) : SailM (BitVec 64) )
  writeReg MDCCINT_EL1 (Sail.BitVec.updateSubrange w__72 28 0 0b00000000000000000000000000000#29)
  let w__73 ← (( do readReg MVFR0_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR0_EL1 (Sail.BitVec.updateSubrange w__73 63 32 0b00000000000000000000000000000000#32)
  let w__74 ← (( do readReg MVFR0_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR0_EL1 (Sail.BitVec.updateSubrange w__74 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__75 ← (( do readReg ICC_HPPIR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_HPPIR1_EL1 (Sail.BitVec.updateSubrange w__75 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__76 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
  writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__76 63 13
    0b000000000000000000000000000000000000000000000000000#51)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__77 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__77 12 12 0#1))
  else
    (do
      let w__78 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__79 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__78 12 12 w__79))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__80 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__80 11 11 0#1))
  else
    (do
      let w__81 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__82 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__81 11 11 w__82))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__83 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__83 10 10 0#1))
  else
    (do
      let w__84 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__85 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__84 10 10 w__85))
  let w__86 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
  writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__86 9 5 0b00000#5)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__87 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__87 4 4 0#1))
  else
    (do
      let w__88 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__89 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__88 4 4 w__89))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__90 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__90 3 3 0#1))
  else
    (do
      let w__91 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__92 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__91 3 3 w__92))
  let w__93 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
  writeReg TCR2_EL2 (BitVec.update w__93 2 (Bit 0#1))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__94 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__94 1 1 0#1))
  else
    (do
      let w__95 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__96 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__95 1 1 w__96))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__97 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__97 0 0 0#1))
  else
    (do
      let w__98 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__99 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__98 0 0 w__99))
  let w__100 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
  writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__100 63 16
    0b000000000000000000000000000000000000000000000000#48)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__101 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__101 13 13 0#1))
  else
    (do
      let w__102 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__103 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__102 13 13 w__103))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__104 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__104 12 12 0#1))
  else
    (do
      let w__105 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__106 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__105 12 12 w__106))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__107 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__107 11 11 0#1))
  else
    (do
      let w__108 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__109 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__108 11 11 w__109))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__110 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__110 10 10 0#1))
  else
    (do
      let w__111 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__112 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__111 10 10 w__112))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__113 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__113 9 8 0b00#2))
  else
    (do
      let w__114 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__115 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__114 9 8 w__115))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__116 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__116 7 6 0b00#2))
  else
    (do
      let w__117 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__118 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__117 7 6 w__118))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__119 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__119 5 5 0#1))
  else
    (do
      let w__120 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__121 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__120 5 5 w__121))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__122 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__122 4 4 0#1))
  else
    (do
      let w__123 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__124 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__123 4 4 w__124))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__125 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__125 3 3 0#1))
  else
    (do
      let w__126 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__127 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__126 3 3 w__127))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__128 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__128 2 2 0#1))
  else
    (do
      let w__129 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__130 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__129 2 2 w__130))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__131 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__131 1 1 0#1))
  else
    (do
      let w__132 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__133 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__132 1 1 w__133))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__134 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__134 0 0 0#1))
  else
    (do
      let w__135 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__136 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__135 0 0 w__136))
  let w__137 ← (( do readReg ESR_EL1 ) : SailM (BitVec 64) )
  writeReg ESR_EL1 (Sail.BitVec.updateSubrange w__137 63 56 0b00000000#8)
  let w__138 ← (( do readReg ICV_BPR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_BPR1_EL1 (Sail.BitVec.updateSubrange w__138 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__139 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  writeReg TCR_EL3 (Sail.BitVec.updateSubrange w__139 63 44 0b00000000000000000000#20)
  let w__140 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  writeReg TCR_EL3 (Sail.BitVec.updateSubrange w__140 40 39 0b00#2)
  let w__141 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  writeReg TCR_EL3 (BitVec.update w__141 31 (Bit 1#1))
  let w__142 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  writeReg TCR_EL3 (BitVec.update w__142 23 (Bit 1#1))
  let w__143 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  writeReg TCR_EL3 (BitVec.update w__143 19 (Bit 0#1))
  let w__144 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  writeReg TCR_EL3 (Sail.BitVec.updateSubrange w__144 7 6 0b00#2)
  let w__145 ← (( do readReg ID_ISAR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR2_EL1 (Sail.BitVec.updateSubrange w__145 63 32
    0b00000000000000000000000000000000#32)
  let w__146 ← (( do readReg ID_ISAR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR2_EL1 (Sail.BitVec.updateSubrange w__146 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__147 ← (( do readReg PMECR_EL1 ) : SailM (BitVec 64) )
  writeReg PMECR_EL1 (Sail.BitVec.updateSubrange w__147 63 5
    0b00000000000000000000000000000000000000000000000000000000000#59)
  if ((cold && true) : Bool)
  then
    (do
      let w__148 ← (( do readReg PMECR_EL1 ) : SailM (BitVec 64) )
      let w__149 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg PMECR_EL1 (Sail.BitVec.updateSubrange w__148 4 3 w__149))
  else
    (do
      if (((cold && (! (HaveEL EL3))) && (! (HaveEL EL2))) : Bool)
      then
        (do
          let w__150 ← (( do readReg PMECR_EL1 ) : SailM (BitVec 64) )
          writeReg PMECR_EL1 (Sail.BitVec.updateSubrange w__150 4 3 0b00#2))
      else (pure (())))
  let w__151 ← (( do readReg ICC_PMR_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_PMR_EL1 (Sail.BitVec.updateSubrange w__151 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__152 ← (( do readReg ICC_PMR_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_PMR_EL1 (Sail.BitVec.updateSubrange w__152 7 0 0b00000000#8)
  let w__153 ← (( do readReg ICV_EOIR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_EOIR1_EL1 (Sail.BitVec.updateSubrange w__153 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__154 ← (( do readReg RMR_EL1 ) : SailM (BitVec 64) )
  writeReg RMR_EL1 (Sail.BitVec.updateSubrange w__154 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__155 ← (( do readReg RMR_EL1 ) : SailM (BitVec 64) )
  writeReg RMR_EL1 (Sail.BitVec.updateSubrange w__155 1 1 0#1)
  let w__156 ← (( do readReg OSLAR_EL1 ) : SailM (BitVec 64) )
  writeReg OSLAR_EL1 (Sail.BitVec.updateSubrange w__156 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__157 ← (( do readReg PMICFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMICFILTR_EL0 (Sail.BitVec.updateSubrange w__157 63 59 0b00000#5)
  let w__158 ← (( do readReg PMICFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMICFILTR_EL0 (Sail.BitVec.updateSubrange w__158 57 32 0b00000000000000000000000000#26)
  let w__159 ← (( do readReg PMICFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMICFILTR_EL0 (BitVec.update w__159 25 (Bit 0#1))
  let w__160 ← (( do readReg PMICFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMICFILTR_EL0 (Sail.BitVec.updateSubrange w__160 19 16 0b0000#4)
  let w__161 ← (( do readReg ICC_HPPIR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_HPPIR0_EL1 (Sail.BitVec.updateSubrange w__161 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__162 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHPS_CTL_EL2 (Sail.BitVec.updateSubrange w__162 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__163 ← (( do readReg VMECID_A_EL2 ) : SailM (BitVec 64) )
  writeReg VMECID_A_EL2 (Sail.BitVec.updateSubrange w__163 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__164 ← (( do readReg MECID_RL_A_EL3 ) : SailM (BitVec 64) )
  writeReg MECID_RL_A_EL3 (Sail.BitVec.updateSubrange w__164 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__165 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange w__165 63 16
    (Sail.BitVec.extractLsb 0b00000000000000000000000000000000000000000000000000#50 49 2))
  let w__166 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange w__166 14 14
    (Sail.BitVec.extractLsb 0b00000000000000000000000000000000000000000000000000#50 1 1))
  let w__167 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange w__167 4 4
    (Sail.BitVec.extractLsb 0b00000000000000000000000000000000000000000000000000#50 0 0))
  let w__168 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange w__168 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__169 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSCLR_EL0 (Sail.BitVec.updateSubrange w__169 63 33
    0b0000000000000000000000000000000#31)
  let w__170 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSCLR_EL0 (BitVec.update w__170 32 (Bit 0#1))
  let w__171 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__171 63 50 0b00000000000000#14)
  let w__172 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__172 49 49
    (Sail.BitVec.extractLsb 0b0000000000000000#16 15 15))
  let w__173 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__173 47 47
    (Sail.BitVec.extractLsb 0b0000000000000000#16 14 14))
  let w__174 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__174 45 45
    (Sail.BitVec.extractLsb 0b0000000000000000#16 13 13))
  let w__175 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__175 43 43
    (Sail.BitVec.extractLsb 0b0000000000000000#16 12 12))
  let w__176 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__176 41 41
    (Sail.BitVec.extractLsb 0b0000000000000000#16 11 11))
  let w__177 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__177 39 39
    (Sail.BitVec.extractLsb 0b0000000000000000#16 10 10))
  let w__178 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__178 37 37
    (Sail.BitVec.extractLsb 0b0000000000000000#16 9 9))
  let w__179 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__179 35 35
    (Sail.BitVec.extractLsb 0b0000000000000000#16 8 8))
  let w__180 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__180 33 33
    (Sail.BitVec.extractLsb 0b0000000000000000#16 7 7))
  let w__181 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__181 31 31
    (Sail.BitVec.extractLsb 0b0000000000000000#16 6 6))
  let w__182 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__182 29 29
    (Sail.BitVec.extractLsb 0b0000000000000000#16 5 5))
  let w__183 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__183 27 27
    (Sail.BitVec.extractLsb 0b0000000000000000#16 4 4))
  let w__184 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__184 25 25
    (Sail.BitVec.extractLsb 0b0000000000000000#16 3 3))
  let w__185 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__185 23 23
    (Sail.BitVec.extractLsb 0b0000000000000000#16 2 2))
  let w__186 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__186 21 21
    (Sail.BitVec.extractLsb 0b0000000000000000#16 1 1))
  let w__187 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__187 19 19
    (Sail.BitVec.extractLsb 0b0000000000000000#16 0 0))
  let w__188 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__188 48 48
    (Sail.BitVec.extractLsb 0b0000000000000000#16 15 15))
  let w__189 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__189 46 46
    (Sail.BitVec.extractLsb 0b0000000000000000#16 14 14))
  let w__190 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__190 44 44
    (Sail.BitVec.extractLsb 0b0000000000000000#16 13 13))
  let w__191 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__191 42 42
    (Sail.BitVec.extractLsb 0b0000000000000000#16 12 12))
  let w__192 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__192 40 40
    (Sail.BitVec.extractLsb 0b0000000000000000#16 11 11))
  let w__193 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__193 38 38
    (Sail.BitVec.extractLsb 0b0000000000000000#16 10 10))
  let w__194 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__194 36 36
    (Sail.BitVec.extractLsb 0b0000000000000000#16 9 9))
  let w__195 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__195 34 34
    (Sail.BitVec.extractLsb 0b0000000000000000#16 8 8))
  let w__196 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__196 32 32
    (Sail.BitVec.extractLsb 0b0000000000000000#16 7 7))
  let w__197 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__197 30 30
    (Sail.BitVec.extractLsb 0b0000000000000000#16 6 6))
  let w__198 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__198 28 28
    (Sail.BitVec.extractLsb 0b0000000000000000#16 5 5))
  let w__199 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__199 26 26
    (Sail.BitVec.extractLsb 0b0000000000000000#16 4 4))
  let w__200 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__200 24 24
    (Sail.BitVec.extractLsb 0b0000000000000000#16 3 3))
  let w__201 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__201 22 22
    (Sail.BitVec.extractLsb 0b0000000000000000#16 2 2))
  let w__202 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__202 20 20
    (Sail.BitVec.extractLsb 0b0000000000000000#16 1 1))
  let w__203 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__203 18 18
    (Sail.BitVec.extractLsb 0b0000000000000000#16 0 0))
  let w__204 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__204 17 17 0#1)
  let w__205 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__205 0 0 0#1)
  let w__206 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__206 16 5 0b000000000000#12)
  let w__207 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__207 4 1 0b0000#4)
  let w__208 ← (( do readReg ICC_BPR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_BPR0_EL1 (Sail.BitVec.updateSubrange w__208 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__209 ← (( do readReg ACCDATA_EL1 ) : SailM (BitVec 64) )
  writeReg ACCDATA_EL1 (Sail.BitVec.updateSubrange w__209 63 32
    0b00000000000000000000000000000000#32)
  let w__210 ← (( do readReg OSDLR_EL1 ) : SailM (BitVec 64) )
  writeReg OSDLR_EL1 (Sail.BitVec.updateSubrange w__210 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__211 ← (( do readReg OSDLR_EL1 ) : SailM (BitVec 64) )
  writeReg OSDLR_EL1 (Sail.BitVec.updateSubrange w__211 0 0 0#1)
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__212 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__212 61 61 0#1))
  else
    (do
      let w__213 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      let w__214 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__213 61 61 w__214))
  let w__215 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (BitVec.update w__215 34 (Bit 0#1))
  let w__216 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (BitVec.update w__216 17 (Bit 0#1))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__217 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__217 12 12 0#1))
  else
    (do
      let w__218 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      let w__219 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__218 12 12 w__219))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__220 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__220 2 2 0#1))
  else
    (do
      let w__221 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      let w__222 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__221 2 2 w__222))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__223 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__223 0 0 0#1))
  else
    (do
      let w__224 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      let w__225 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__224 0 0 w__225))
  let w__226 ← (( do readReg PMSSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSSCR_EL1 (Sail.BitVec.updateSubrange w__226 63 33 0b0000000000000000000000000000000#31)
  let w__227 ← (( do readReg PMSSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSSCR_EL1 (Sail.BitVec.updateSubrange w__227 32 32 1#1)
  let w__228 ← (( do readReg PMSSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSSCR_EL1 (Sail.BitVec.updateSubrange w__228 31 1 0b0000000000000000000000000000000#31)
  let w__229 ← (( do readReg PMSSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSSCR_EL1 (Sail.BitVec.updateSubrange w__229 0 0 0#1)
  let w__230 ← (( do readReg LORID_EL1 ) : SailM (BitVec 64) )
  writeReg LORID_EL1 (Sail.BitVec.updateSubrange w__230 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__231 ← (( do readReg LORID_EL1 ) : SailM (BitVec 64) )
  writeReg LORID_EL1 (Sail.BitVec.updateSubrange w__231 15 8 0b00000000#8)
  let w__232 ← (( do readReg CONTEXTIDR_EL2 ) : SailM (BitVec 64) )
  writeReg CONTEXTIDR_EL2 (Sail.BitVec.updateSubrange w__232 63 32
    0b00000000000000000000000000000000#32)
  let w__233 ← (( do readReg FPSR ) : SailM (BitVec 64) )
  writeReg FPSR (Sail.BitVec.updateSubrange w__233 63 32 0b00000000000000000000000000000000#32)
  let w__234 ← (( do readReg FPSR ) : SailM (BitVec 64) )
  writeReg FPSR (Sail.BitVec.updateSubrange w__234 26 8 0b0000000000000000000#19)
  let w__235 ← (( do readReg FPSR ) : SailM (BitVec 64) )
  writeReg FPSR (Sail.BitVec.updateSubrange w__235 6 5 0b00#2)
  let w__236 ← (( do readReg CNTP_TVAL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTP_TVAL_EL0 (Sail.BitVec.updateSubrange w__236 63 32
    0b00000000000000000000000000000000#32)
  let w__237 ← (( do readReg ID_AA64MMFR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR4_EL1 (Sail.BitVec.updateSubrange w__237 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__238 ← (( do readReg ID_AA64MMFR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR4_EL1 (Sail.BitVec.updateSubrange w__238 3 0 0b0000#4)
  let w__239 ← (( do readReg ICH_EISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_EISR_EL2 (Sail.BitVec.updateSubrange w__239 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__240 ← (( do readReg MIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MIDR_EL1 (Sail.BitVec.updateSubrange w__240 63 32 0b00000000000000000000000000000000#32)
  let w__241 ← (( do readReg ICC_RPR_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_RPR_EL1 (Sail.BitVec.updateSubrange w__241 61 8
    0b000000000000000000000000000000000000000000000000000000#54)
  let w__242 ← (( do readReg ICH_ELRSR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_ELRSR_EL2 (Sail.BitVec.updateSubrange w__242 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__243 ← (( do readReg VBAR_EL2 ) : SailM (BitVec 64) )
  writeReg VBAR_EL2 (Sail.BitVec.updateSubrange w__243 10 0 0b00000000000#11)
  let w__244 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__244 63 61 0b000#3)
  let w__245 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__245 60 60 0#1)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__246 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__246 59 59 0#1))
  else
    (do
      let w__247 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
      let w__248 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__247 59 59 w__248))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__249 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__249 58 58 0#1))
  else
    (do
      let w__250 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
      let w__251 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__250 58 58 w__251))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__252 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__252 57 57 0#1))
  else
    (do
      let w__253 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
      let w__254 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__253 57 57 w__254))
  let w__255 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__255 56 56 0#1)
  let w__256 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__256 55 55 0#1)
  let w__257 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__257 54 54 0#1)
  let w__258 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__258 53 53 0#1)
  let w__259 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__259 52 52 0#1)
  let w__260 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__260 51 51 0#1)
  let w__261 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__261 50 50 0#1)
  let w__262 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__262 49 49 0#1)
  let w__263 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__263 48 48 0#1)
  let w__264 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__264 47 47 0#1)
  let w__265 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__265 46 46 0#1)
  let w__266 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__266 45 45 0#1)
  let w__267 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__267 44 44 0#1)
  let w__268 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__268 43 43 0#1)
  let w__269 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__269 42 42 0#1)
  let w__270 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__270 41 41 0#1)
  let w__271 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__271 40 40 0#1)
  let w__272 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__272 39 39 0#1)
  let w__273 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__273 38 38 0#1)
  let w__274 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__274 37 37 0#1)
  let w__275 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__275 36 36 0#1)
  let w__276 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__276 35 35 0#1)
  let w__277 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__277 34 34 0#1)
  let w__278 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__278 33 33 0#1)
  let w__279 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__279 32 32 0#1)
  let w__280 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__280 31 31 0#1)
  let w__281 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__281 30 30 0#1)
  let w__282 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__282 29 29 0#1)
  let w__283 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__283 28 28 0#1)
  let w__284 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__284 27 27 0#1)
  let w__285 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__285 26 26 0#1)
  let w__286 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__286 25 25 0#1)
  let w__287 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__287 24 24 0#1)
  let w__288 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__288 23 23 0#1)
  let w__289 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__289 22 22 0#1)
  let w__290 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__290 21 21 0#1)
  let w__291 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__291 20 20 0#1)
  let w__292 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__292 19 19 0#1)
  let w__293 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__293 18 18 0#1)
  let w__294 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__294 17 17 0#1)
  let w__295 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__295 16 16 0#1)
  let w__296 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__296 15 15 0#1)
  let w__297 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__297 14 14 0#1)
  let w__298 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__298 13 13 0#1)
  let w__299 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__299 12 12 0#1)
  let w__300 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__300 11 11 0#1)
  let w__301 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__301 10 10 0#1)
  let w__302 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__302 9 9 0#1)
  let w__303 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__303 8 8 0#1)
  let w__304 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__304 7 7 0#1)
  let w__305 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__305 6 6 0#1)
  let w__306 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__306 5 5 0#1)
  let w__307 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__307 4 4 0#1)
  (pure true)


end ArmFull.Functions
