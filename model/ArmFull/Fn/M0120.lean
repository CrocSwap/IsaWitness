import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0020
import ArmFull.Fn.M0034
import ArmFull.Fn.M0041
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051

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

def AArch64_S2StartLevel (walkparams : S2TTWParams) : SailM Int := do
  let descsizelog2 ← (( do (undefined_int_at (← occLabel 1542) ()) ) : SailM Int )
  let granulebits ← (( do (undefined_int_at (← occLabel 1543) ()) ) : SailM Int )
  let iasize ← (( do (undefined_int_at (← occLabel 1544) ()) ) : SailM Int )
  let s2startlevel ← (( do (undefined_int_at (← occLabel 1545) ()) ) : SailM Int )
  let stride ← (( do (undefined_int_at (← occLabel 1546) ()) ) : SailM Int )
  if ((walkparams.d128 == 1#1) : Bool)
  then
    (let iasize : Int := (AArch64_IASize walkparams.txsz)
    let granulebits : Int := (TGxGranuleBits walkparams.tgx)
    let descsizelog2 : Nat := 4
    let stride : Int := (granulebits -i descsizelog2)
    let s2startlevel : Int := (FINAL_LEVEL -i (fdiv_int ((iasize -i 1) -i granulebits) stride))
    let s2startlevel : Int := (s2startlevel +i (BitVec.toNat walkparams.skl))
    (pure (s2startlevel)))
  else
    (do
      match walkparams.tgx with
      | .TGx_4KB =>
        (do
          match (BitVec.setWidth 3 (walkparams.sl2 +++ walkparams.sl0)) with
          | 0b000 => (pure (2))
          | 0b001 => (pure (1))
          | 0b010 => (pure (0))
          | 0b011 => (pure (3))
          | 0b100 => (pure ((Neg.neg 1)))
          | _ =>
            (do
              (undefined_int_at (← occLabel 1547) ())))
      | .TGx_16KB =>
        (do
          match walkparams.sl0 with
          | 0b00 => (pure (3))
          | 0b01 => (pure (2))
          | 0b10 => (pure (1))
          | 0b11 => (pure (0))
          | _ =>
            (do
              (undefined_int_at (← occLabel 1548) ())))
      | .TGx_64KB =>
        (do
          match walkparams.sl0 with
          | 0b00 => (pure (3))
          | 0b01 => (pure (2))
          | 0b10 => (pure (1))
          | _ =>
            (do
              (undefined_int_at (← occLabel 1549) ()))))


def AArch64_SettingAccessFlagPermitted (fault : FaultRecord) : SailM Bool := do
  if ((BEq.beq fault.statuscode Fault_None) : Bool)
  then (pure (true))
  else
    (do
      if (((BEq.beq fault.statuscode Fault_Alignment) || (BEq.beq fault.statuscode Fault_Permission)) : Bool)
      then
        (do
          (ConstrainUnpredictableBool Unpredictable_AFUPDATE))
      else (pure (false)))


def AArch64_SettingDirtyStatePermitted (fault : FaultRecord) : SailM Bool := do
  if ((BEq.beq fault.statuscode Fault_None) : Bool)
  then (pure (true))
  else
    (do
      if ((BEq.beq fault.statuscode Fault_Alignment) : Bool)
      then
        (do
          (ConstrainUnpredictableBool Unpredictable_DBUPDATE))
      else (pure (false)))


/-- Type quantifiers: counter_index : Nat, 0 ≤ counter_index ∨ (not (counter_index < 32)) -/
def SPEStartCounter (counter_index : Nat) : SailM Unit := do
  ArmFull.assert (counter_index <b SPEMaxCounters) "sail-arm/v8_base.sail:27796.41-27796.42"
  let w__0 ← (( do readReg SPESampleCounterPending ) : SailM (Vector Bool 32) )
  writeReg SPESampleCounterPending (vectorUpdate w__0 counter_index true)


def _set_RCWMASK_EL1_Type_Mask (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_RCWMASK_EL1_Type_Mask r v)


def _set_RCWSMASK_EL1_Type_Software_Mask (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 128)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_RCWSMASK_EL1_Type_Software_Mask r v)


def AddressSupportsLS64 (paddress : (BitVec 56)) : SailM Bool := do
  (__UNKNOWN_boolean ())


def ResetSMEState (_ : Unit) : SailM Unit := do
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv MAX_VL 8)))
  let loop_n_lower : Nat := 0
  let loop_n_upper : Int := (vectors_name -i 1)
  (do
    let mut loop_vars := ()
    for n in [loop_n_lower:loop_n_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do readReg _ZA ) : SailM (Vector (BitVec 2048) 256) )
        writeReg _ZA (vectorUpdate w__0 (Sail.Int.toNatChecked (n))
          (Sail.BitVec.castWidth (m := 2048) (Zeros (n := MAX_VL))))
    (pure loop_vars))
  writeReg _ZT0 (Sail.BitVec.castWidth (m := 512) (Zeros (n := ZT0_LEN)))


/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 -/
def FirstActive (mask : (BitVec k_N)) (x : (BitVec k_N)) (esize : Int) : SailM (BitVec 1) := SailME.run do
  let elements : Int := (fdiv_int (Sail.BitVec.length x) (fdiv_int esize 8))
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailME (BitVec 1) Bool )
        if (w__0 : Bool)
        then
          (do
            let w__1 ← (( do (PredicateElement x e esize) ) : SailME (BitVec 1) (BitVec 1) )
            SailME.throw (w__1 : (BitVec 1)))
        else (pure (()))
    (pure loop_vars))
  (pure (0#1))


/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 -/
def LastActive (mask : (BitVec k_N)) (x : (BitVec k_N)) (esize : Int) : SailM (BitVec 1) := SailME.run do
  let elements : Int := (fdiv_int (Sail.BitVec.length x) (fdiv_int esize 8))
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_upper:loop_e_lower:-1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailME (BitVec 1) Bool )
        if (w__0 : Bool)
        then
          (do
            let w__1 ← (( do (PredicateElement x e esize) ) : SailME (BitVec 1) (BitVec 1) )
            SailME.throw (w__1 : (BitVec 1)))
        else (pure (()))
    (pure loop_vars))
  (pure (0#1))


/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 -/
def NoneActive (mask : (BitVec k_N)) (x : (BitVec k_N)) (esize : Int) : SailM (BitVec 1) := SailME.run do
  let elements : Int := (fdiv_int (Sail.BitVec.length x) (fdiv_int esize 8))
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__2 ← (( do
          if ((← do
               (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              (ActivePredicateElement x e esize))
          else (pure false) ) : SailME (BitVec 1) Bool )
        if (w__2 : Bool)
        then
          (do
            SailME.throw (0#1 : (BitVec 1)))
        else (pure (()))
    (pure loop_vars))
  (pure (1#1))


/-- Type quantifiers: e : Int, esize : Int -/
def ElemFFR_read (e : Int) (esize : Int) : SailM (BitVec 1) := do
  let w__0 ← (( do readReg _FFR ) : SailM (BitVec 256) )
  (PredicateElement w__0 e esize)


/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 -/
def LastActiveElement (mask : (BitVec k_N)) (esize : Int) : SailM Int := SailME.run do
  let elements : Int := (fdiv_int (Sail.BitVec.length mask) (fdiv_int esize 8))
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_upper:loop_e_lower:-1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailME Int Bool )
        if (w__0 : Bool)
        then
          (do
            SailME.throw (e : Int))
        else (pure (()))
    (pure loop_vars))
  (pure ((Neg.neg 1)))


/-- Type quantifiers: M : Int, k_N : Nat, k_N ≥ 0 -/
def Reverse (word : (BitVec k_N)) (M : Int) : SailM (BitVec k_N) := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1735)
      (Sail.BitVec.length word))) ) : SailM (BitVec k_N) )
  let sw : Int := (fdiv_int (Sail.BitVec.length word) M)
  ArmFull.assert ((Sail.BitVec.length word) == (sw *i M)) "sail-arm/v8_base.sail:29989.23-29989.24"
  let loop_s_lower : Nat := 0
  let loop_s_upper : Int := (sw -i 1)
  (do
    let mut loop_vars := result
    for s in [loop_s_lower:loop_s_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        ArmFull.assert (((s *i M) ≤b (((s *i M) +i M) -i 1)) || (! ((s ≥b 0) && (((s +i 1) *i M) ≤b (Sail.BitVec.length
                  word))))) "sail-arm/v8_base.sail:29991.115-29991.116"
        let w__0 ← (( do
          ((Sail.BitVec.castWidth ) <$> (Elem_read word s (Sail.Int.toNatChecked (M)))) ) : SailM
          (BitVec (Sail.Int.toNatChecked (M : Int))) )
        (Elem_set result ((sw -i 1) -i s) (Sail.Int.toNatChecked (M)) (Sail.BitVec.castWidth w__0))
    (pure loop_vars))


/-- Type quantifiers: N : Nat, index : Int, List.elem N [16, 32, 64] -/
def FPTrigMAddCoefficient_read (index : Int) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-arm/v8_base.sail:30034.38-30034.39"
  let result ← (( do (undefined_int_at (← occLabel 1740) ()) ) : SailM Int )
  let result : Int :=
    if ((N == 16) : Bool)
    then
      (match index with
      | 0 => (BitVec.toNat 0x3C00#16)
      | 1 => (BitVec.toNat 0xB155#16)
      | 2 => (BitVec.toNat 0x2030#16)
      | 3 => (BitVec.toNat 0x0000#16)
      | 4 => (BitVec.toNat 0x0000#16)
      | 5 => (BitVec.toNat 0x0000#16)
      | 6 => (BitVec.toNat 0x0000#16)
      | 7 => (BitVec.toNat 0x0000#16)
      | 8 => (BitVec.toNat 0x3C00#16)
      | 9 => (BitVec.toNat 0xB800#16)
      | 10 => (BitVec.toNat 0x293A#16)
      | 11 => (BitVec.toNat 0x0000#16)
      | 12 => (BitVec.toNat 0x0000#16)
      | 13 => (BitVec.toNat 0x0000#16)
      | 14 => (BitVec.toNat 0x0000#16)
      | 15 => (BitVec.toNat 0x0000#16)
      | _ => result)
    else
      (if ((N == 32) : Bool)
      then
        (match index with
        | 0 => (BitVec.toNat 0x3F800000#32)
        | 1 => (BitVec.toNat 0xBE2AAAAB#32)
        | 2 => (BitVec.toNat 0x3C088886#32)
        | 3 => (BitVec.toNat 0xB95008B9#32)
        | 4 => (BitVec.toNat 0x36369D6D#32)
        | 5 => (BitVec.toNat 0x00000000#32)
        | 6 => (BitVec.toNat 0x00000000#32)
        | 7 => (BitVec.toNat 0x00000000#32)
        | 8 => (BitVec.toNat 0x3F800000#32)
        | 9 => (BitVec.toNat 0xBF000000#32)
        | 10 => (BitVec.toNat 0x3D2AAAA6#32)
        | 11 => (BitVec.toNat 0xBAB60705#32)
        | 12 => (BitVec.toNat 0x37CD37CC#32)
        | 13 => (BitVec.toNat 0x00000000#32)
        | 14 => (BitVec.toNat 0x00000000#32)
        | 15 => (BitVec.toNat 0x00000000#32)
        | _ => result)
      else
        (match index with
        | 0 => (BitVec.toNat 0x3FF0000000000000#64)
        | 1 => (BitVec.toNat 0xBFC5555555555543#64)
        | 2 => (BitVec.toNat 0x3F8111111110F30C#64)
        | 3 => (BitVec.toNat 0xBF2A01A019B92FC6#64)
        | 4 => (BitVec.toNat 0x3EC71DE351F3D22B#64)
        | 5 => (BitVec.toNat 0xBE5AE5E2B60F7B91#64)
        | 6 => (BitVec.toNat 0x3DE5D8408868552F#64)
        | 7 => (BitVec.toNat 0x0000000000000000#64)
        | 8 => (BitVec.toNat 0x3FF0000000000000#64)
        | 9 => (BitVec.toNat 0xBFE0000000000000#64)
        | 10 => (BitVec.toNat 0x3FA5555555555536#64)
        | 11 => (BitVec.toNat 0xBF56C16C16C13A0B#64)
        | 12 => (BitVec.toNat 0x3EFA01A019B1E8D8#64)
        | 13 => (BitVec.toNat 0xBE927E4F7282F468#64)
        | 14 => (BitVec.toNat 0x3E21EE96D2641B13#64)
        | 15 => (BitVec.toNat 0xBDA8F76380FBB401#64)
        | _ => result))
  let result : Int := result
  (pure ((Sail.BitVec.castWidth (integer_subrange result (N -i 1) 0))))


/-- Type quantifiers: N : Nat, index : Int, List.elem N [16, 32, 64] -/
def FPExpCoefficient_read (index : Int) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-arm/v8_base.sail:30222.38-30222.39"
  let result ← (( do (undefined_int_at (← occLabel 1741) ()) ) : SailM Int )
  let result : Int :=
    if ((N == 16) : Bool)
    then
      (match index with
      | 0 => (BitVec.toNat 0x0000#16)
      | 1 => (BitVec.toNat 0x0016#16)
      | 2 => (BitVec.toNat 0x002D#16)
      | 3 => (BitVec.toNat 0x0045#16)
      | 4 => (BitVec.toNat 0x005D#16)
      | 5 => (BitVec.toNat 0x0075#16)
      | 6 => (BitVec.toNat 0x008E#16)
      | 7 => (BitVec.toNat 0x00A8#16)
      | 8 => (BitVec.toNat 0x00C2#16)
      | 9 => (BitVec.toNat 0x00DC#16)
      | 10 => (BitVec.toNat 0x00F8#16)
      | 11 => (BitVec.toNat 0x0114#16)
      | 12 => (BitVec.toNat 0x0130#16)
      | 13 => (BitVec.toNat 0x014D#16)
      | 14 => (BitVec.toNat 0x016B#16)
      | 15 => (BitVec.toNat 0x0189#16)
      | 16 => (BitVec.toNat 0x01A8#16)
      | 17 => (BitVec.toNat 0x01C8#16)
      | 18 => (BitVec.toNat 0x01E8#16)
      | 19 => (BitVec.toNat 0x0209#16)
      | 20 => (BitVec.toNat 0x022B#16)
      | 21 => (BitVec.toNat 0x024E#16)
      | 22 => (BitVec.toNat 0x0271#16)
      | 23 => (BitVec.toNat 0x0295#16)
      | 24 => (BitVec.toNat 0x02BA#16)
      | 25 => (BitVec.toNat 0x02E0#16)
      | 26 => (BitVec.toNat 0x0306#16)
      | 27 => (BitVec.toNat 0x032E#16)
      | 28 => (BitVec.toNat 0x0356#16)
      | 29 => (BitVec.toNat 0x037F#16)
      | 30 => (BitVec.toNat 0x03A9#16)
      | 31 => (BitVec.toNat 0x03D4#16)
      | _ => result)
    else
      (if ((N == 32) : Bool)
      then
        (match index with
        | 0 => (BitVec.toNat 0x000000#24)
        | 1 => (BitVec.toNat 0x0164D2#24)
        | 2 => (BitVec.toNat 0x02CD87#24)
        | 3 => (BitVec.toNat 0x043A29#24)
        | 4 => (BitVec.toNat 0x05AAC3#24)
        | 5 => (BitVec.toNat 0x071F62#24)
        | 6 => (BitVec.toNat 0x08980F#24)
        | 7 => (BitVec.toNat 0x0A14D5#24)
        | 8 => (BitVec.toNat 0x0B95C2#24)
        | 9 => (BitVec.toNat 0x0D1ADF#24)
        | 10 => (BitVec.toNat 0x0EA43A#24)
        | 11 => (BitVec.toNat 0x1031DC#24)
        | 12 => (BitVec.toNat 0x11C3D3#24)
        | 13 => (BitVec.toNat 0x135A2B#24)
        | 14 => (BitVec.toNat 0x14F4F0#24)
        | 15 => (BitVec.toNat 0x16942D#24)
        | 16 => (BitVec.toNat 0x1837F0#24)
        | 17 => (BitVec.toNat 0x19E046#24)
        | 18 => (BitVec.toNat 0x1B8D3A#24)
        | 19 => (BitVec.toNat 0x1D3EDA#24)
        | 20 => (BitVec.toNat 0x1EF532#24)
        | 21 => (BitVec.toNat 0x20B051#24)
        | 22 => (BitVec.toNat 0x227043#24)
        | 23 => (BitVec.toNat 0x243516#24)
        | 24 => (BitVec.toNat 0x25FED7#24)
        | 25 => (BitVec.toNat 0x27CD94#24)
        | 26 => (BitVec.toNat 0x29A15B#24)
        | 27 => (BitVec.toNat 0x2B7A3A#24)
        | 28 => (BitVec.toNat 0x2D583F#24)
        | 29 => (BitVec.toNat 0x2F3B79#24)
        | 30 => (BitVec.toNat 0x3123F6#24)
        | 31 => (BitVec.toNat 0x3311C4#24)
        | 32 => (BitVec.toNat 0x3504F3#24)
        | 33 => (BitVec.toNat 0x36FD92#24)
        | 34 => (BitVec.toNat 0x38FBAF#24)
        | 35 => (BitVec.toNat 0x3AFF5B#24)
        | 36 => (BitVec.toNat 0x3D08A4#24)
        | 37 => (BitVec.toNat 0x3F179A#24)
        | 38 => (BitVec.toNat 0x412C4D#24)
        | 39 => (BitVec.toNat 0x4346CD#24)
        | 40 => (BitVec.toNat 0x45672A#24)
        | 41 => (BitVec.toNat 0x478D75#24)
        | 42 => (BitVec.toNat 0x49B9BE#24)
        | 43 => (BitVec.toNat 0x4BEC15#24)
        | 44 => (BitVec.toNat 0x4E248C#24)
        | 45 => (BitVec.toNat 0x506334#24)
        | 46 => (BitVec.toNat 0x52A81E#24)
        | 47 => (BitVec.toNat 0x54F35B#24)
        | 48 => (BitVec.toNat 0x5744FD#24)
        | 49 => (BitVec.toNat 0x599D16#24)
        | 50 => (BitVec.toNat 0x5BFBB8#24)
        | 51 => (BitVec.toNat 0x5E60F5#24)
        | 52 => (BitVec.toNat 0x60CCDF#24)
        | 53 => (BitVec.toNat 0x633F89#24)
        | 54 => (BitVec.toNat 0x65B907#24)
        | 55 => (BitVec.toNat 0x68396A#24)
        | 56 => (BitVec.toNat 0x6AC0C7#24)
        | 57 => (BitVec.toNat 0x6D4F30#24)
        | 58 => (BitVec.toNat 0x6FE4BA#24)
        | 59 => (BitVec.toNat 0x728177#24)
        | 60 => (BitVec.toNat 0x75257D#24)
        | 61 => (BitVec.toNat 0x77D0DF#24)
        | 62 => (BitVec.toNat 0x7A83B3#24)
        | 63 => (BitVec.toNat 0x7D3E0C#24)
        | _ => result)
      else
        (match index with
        | 0 => (BitVec.toNat 0x0000000000000#52)
        | 1 => (BitVec.toNat 0x02C9A3E778061#52)
        | 2 => (BitVec.toNat 0x059B0D3158574#52)
        | 3 => (BitVec.toNat 0x0874518759BC8#52)
        | 4 => (BitVec.toNat 0x0B5586CF9890F#52)
        | 5 => (BitVec.toNat 0x0E3EC32D3D1A2#52)
        | 6 => (BitVec.toNat 0x11301D0125B51#52)
        | 7 => (BitVec.toNat 0x1429AAEA92DE0#52)
        | 8 => (BitVec.toNat 0x172B83C7D517B#52)
        | 9 => (BitVec.toNat 0x1A35BEB6FCB75#52)
        | 10 => (BitVec.toNat 0x1D4873168B9AA#52)
        | 11 => (BitVec.toNat 0x2063B88628CD6#52)
        | 12 => (BitVec.toNat 0x2387A6E756238#52)
        | 13 => (BitVec.toNat 0x26B4565E27CDD#52)
        | 14 => (BitVec.toNat 0x29E9DF51FDEE1#52)
        | 15 => (BitVec.toNat 0x2D285A6E4030B#52)
        | 16 => (BitVec.toNat 0x306FE0A31B715#52)
        | 17 => (BitVec.toNat 0x33C08B26416FF#52)
        | 18 => (BitVec.toNat 0x371A7373AA9CB#52)
        | 19 => (BitVec.toNat 0x3A7DB34E59FF7#52)
        | 20 => (BitVec.toNat 0x3DEA64C123422#52)
        | 21 => (BitVec.toNat 0x4160A21F72E2A#52)
        | 22 => (BitVec.toNat 0x44E086061892D#52)
        | 23 => (BitVec.toNat 0x486A2B5C13CD0#52)
        | 24 => (BitVec.toNat 0x4BFDAD5362A27#52)
        | 25 => (BitVec.toNat 0x4F9B2769D2CA7#52)
        | 26 => (BitVec.toNat 0x5342B569D4F82#52)
        | 27 => (BitVec.toNat 0x56F4736B527DA#52)
        | 28 => (BitVec.toNat 0x5AB07DD485429#52)
        | 29 => (BitVec.toNat 0x5E76F15AD2148#52)
        | 30 => (BitVec.toNat 0x6247EB03A5585#52)
        | 31 => (BitVec.toNat 0x6623882552225#52)
        | 32 => (BitVec.toNat 0x6A09E667F3BCD#52)
        | 33 => (BitVec.toNat 0x6DFB23C651A2F#52)
        | 34 => (BitVec.toNat 0x71F75E8EC5F74#52)
        | 35 => (BitVec.toNat 0x75FEB564267C9#52)
        | 36 => (BitVec.toNat 0x7A11473EB0187#52)
        | 37 => (BitVec.toNat 0x7E2F336CF4E62#52)
        | 38 => (BitVec.toNat 0x82589994CCE13#52)
        | 39 => (BitVec.toNat 0x868D99B4492ED#52)
        | 40 => (BitVec.toNat 0x8ACE5422AA0DB#52)
        | 41 => (BitVec.toNat 0x8F1AE99157736#52)
        | 42 => (BitVec.toNat 0x93737B0CDC5E5#52)
        | 43 => (BitVec.toNat 0x97D829FDE4E50#52)
        | 44 => (BitVec.toNat 0x9C49182A3F090#52)
        | 45 => (BitVec.toNat 0xA0C667B5DE565#52)
        | 46 => (BitVec.toNat 0xA5503B23E255D#52)
        | 47 => (BitVec.toNat 0xA9E6B5579FDBF#52)
        | 48 => (BitVec.toNat 0xAE89F995AD3AD#52)
        | 49 => (BitVec.toNat 0xB33A2B84F15FB#52)
        | 50 => (BitVec.toNat 0xB7F76F2FB5E47#52)
        | 51 => (BitVec.toNat 0xBCC1E904BC1D2#52)
        | 52 => (BitVec.toNat 0xC199BDD85529C#52)
        | 53 => (BitVec.toNat 0xC67F12E57D14B#52)
        | 54 => (BitVec.toNat 0xCB720DCEF9069#52)
        | 55 => (BitVec.toNat 0xD072D4A07897C#52)
        | 56 => (BitVec.toNat 0xD5818DCFBA487#52)
        | 57 => (BitVec.toNat 0xDA9E603DB3285#52)
        | 58 => (BitVec.toNat 0xDFC97337B9B5F#52)
        | 59 => (BitVec.toNat 0xE502EE78B3FF6#52)
        | 60 => (BitVec.toNat 0xEA4AFA2A490DA#52)
        | 61 => (BitVec.toNat 0xEFA1BEE615A27#52)
        | 62 => (BitVec.toNat 0xF50765B6E4540#52)
        | 63 => (BitVec.toNat 0xFA7C1819E90D8#52)
        | _ => result))
  let result : Int := result
  (pure ((Sail.BitVec.castWidth (integer_subrange result (N -i 1) 0))))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BitDeposit (data : (BitVec k_N)) (mask : (BitVec k_N)) : SailM (BitVec k_N) := do
  let res : (BitVec k_N) := (Sail.BitVec.castWidth (Zeros (n := (Sail.BitVec.length mask))))
  let db : Int := 0
  let (db, res) ← (( do
    let loop_rb_lower : Nat := 0
    let loop_rb_upper : Int := ((Sail.BitVec.length res) -i 1)
    (do
      let mut loop_vars := (db, res)
      for rb in [loop_rb_lower:loop_rb_upper:1]i do
        let (db, res) := loop_vars
        loop_vars ← do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access mask (Sail.Int.toNatChecked (rb)))])) == 1#1) : Bool)
          then
            (do
              let db : Int := db
              ArmFull.assert ((0 ≤b db) && (db <b (Sail.BitVec.length res))) "sail-arm/v8_base.sail:31027.58-31027.59"
              let res : (BitVec k_N) :=
                (BitVec.update res (Sail.Int.toNatChecked (rb))
                  (Bit
                    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access data
                        (Sail.Int.toNatChecked (db)))]))))
              let db : Int := (db +i 1)
              (pure ((db, res))))
          else (pure ((db, res)))
      (pure loop_vars)) ) : SailM (Int × (BitVec k_N)) )
  (pure ((Sail.BitVec.castWidth res)))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BitExtract (data : (BitVec k_N)) (mask : (BitVec k_N)) : SailM (BitVec k_N) := do
  let res : (BitVec k_N) := (Sail.BitVec.castWidth (Zeros (n := (Sail.BitVec.length mask))))
  let rb : Int := 0
  let (rb, res) ← (( do
    let loop_db_lower : Nat := 0
    let loop_db_upper : Int := ((Sail.BitVec.length res) -i 1)
    (do
      let mut loop_vars := (rb, res)
      for db in [loop_db_lower:loop_db_upper:1]i do
        let (rb, res) := loop_vars
        loop_vars ← do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access mask (Sail.Int.toNatChecked (db)))])) == 1#1) : Bool)
          then
            (do
              let rb : Int := rb
              ArmFull.assert ((0 ≤b rb) && (rb <b (Sail.BitVec.length res))) "sail-arm/v8_base.sail:31046.58-31046.59"
              let res : (BitVec k_N) :=
                (BitVec.update res (Sail.Int.toNatChecked (rb))
                  (Bit
                    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access data
                        (Sail.Int.toNatChecked (db)))]))))
              let rb : Int := (rb +i 1)
              (pure ((rb, res))))
          else (pure ((rb, res)))
      (pure loop_vars)) ) : SailM (Int × (BitVec k_N)) )
  (pure ((Sail.BitVec.castWidth res)))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BitGroup (data : (BitVec k_N)) (mask : (BitVec k_N)) : SailM (BitVec k_N) := do
  let res ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1746)
      (Sail.BitVec.length mask))) ) : SailM (BitVec k_N) )
  let rb : Int := 0
  let (rb, res) ← (( do
    let loop_db_lower : Nat := 0
    let loop_db_upper : Int := ((Sail.BitVec.length res) -i 1)
    (do
      let mut loop_vars := (rb, res)
      for db in [loop_db_lower:loop_db_upper:1]i do
        let (rb, res) := loop_vars
        loop_vars ← do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access mask (Sail.Int.toNatChecked (db)))])) == 1#1) : Bool)
          then
            (do
              let rb : Int := rb
              ArmFull.assert ((0 ≤b rb) && (rb <b (Sail.BitVec.length res))) "sail-arm/v8_base.sail:31065.58-31065.59"
              let res : (BitVec k_N) :=
                (BitVec.update res (Sail.Int.toNatChecked (rb))
                  (Bit
                    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access data
                        (Sail.Int.toNatChecked (db)))]))))
              let rb : Int := (rb +i 1)
              (pure ((rb, res))))
          else (pure ((rb, res)))
      (pure loop_vars)) ) : SailM (Int × (BitVec k_N)) )
  let (rb, res) ← (( do
    let loop_db_lower : Nat := 0
    let loop_db_upper : Int := ((Sail.BitVec.length res) -i 1)
    (do
      let mut loop_vars := (rb, res)
      for db in [loop_db_lower:loop_db_upper:1]i do
        let (rb, res) := loop_vars
        loop_vars ← do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access mask (Sail.Int.toNatChecked (db)))])) == 0#1) : Bool)
          then
            (do
              let rb : Int := rb
              ArmFull.assert ((0 ≤b rb) && (rb <b (Sail.BitVec.length res))) "sail-arm/v8_base.sail:31076.58-31076.59"
              let res : (BitVec k_N) :=
                (BitVec.update res (Sail.Int.toNatChecked (rb))
                  (Bit
                    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access data
                        (Sail.Int.toNatChecked (db)))]))))
              let rb : Int := (rb +i 1)
              (pure ((rb, res))))
          else (pure ((rb, res)))
      (pure loop_vars)) ) : SailM (Int × (BitVec k_N)) )
  (pure ((Sail.BitVec.castWidth res)))


def GetCurrentGCSPointer (_ : Unit) : SailM (BitVec 64) := do
  let ptr ← (( do (undefined_bitvector_at (← occLabel 1759) 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__0.EL
  if ((questionMark == EL0) : Bool)
  then
    (do
      let w__1 ← (( do readReg GCSPR_EL0 ) : SailM (BitVec 64) )
      let ptr := (((_get_GCSPR_EL0_Type_PTR w__1) +++ 0b000#3) : (BitVec 64))
      (pure (ptr)))
  else
    (do
      if ((questionMark == EL1) : Bool)
      then
        (do
          let w__2 ← (( do readReg GCSPR_EL1 ) : SailM (BitVec 64) )
          let ptr := (((_get_GCSPR_EL1_Type_PTR w__2) +++ 0b000#3) : (BitVec 64))
          (pure (ptr)))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__3 ← (( do readReg GCSPR_EL2 ) : SailM (BitVec 64) )
              let ptr := (((_get_GCSPR_EL2_Type_PTR w__3) +++ 0b000#3) : (BitVec 64))
              (pure (ptr)))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  let w__4 ← (( do readReg GCSPR_EL3 ) : SailM (BitVec 64) )
                  let ptr := (((_get_GCSPR_EL3_Type_PTR w__4) +++ 0b000#3) : (BitVec 64))
                  (pure (ptr)))
              else (pure (ptr)))))


end ArmFull.Functions
