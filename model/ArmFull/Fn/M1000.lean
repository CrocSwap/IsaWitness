import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0917
import ArmFull.Fn.M0918
import ArmFull.Fn.M0919
import ArmFull.Fn.M0923

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

def decode_MOVAZ_MZ2_ZA_D1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 3)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 2
  let esize : Nat := 64
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Nat := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVAZ_MZ2_ZA_D1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_MZ2_ZA_D1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_MZ2_ZA_D1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_MZ2_ZA_D1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_MZ2_ZA_D1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVAZ_MZ4_ZA_B1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (off2 : (BitVec 2)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 4
  let esize : Nat := 8
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let n : Nat := 0
  let offset : Int := (BitVec.toNat (off2 +++ 0b00#2))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVAZ_MZ4_ZA_B1 128 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_MZ4_ZA_B1 256 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_MZ4_ZA_B1 512 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_MZ4_ZA_B1 1024 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_MZ4_ZA_B1 2048 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVAZ_MZ4_ZA_H1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 1)) (o1 : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 4
  let esize : Nat := 16
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVAZ_MZ4_ZA_H1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_MZ4_ZA_H1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_MZ4_ZA_H1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_MZ4_ZA_H1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_MZ4_ZA_H1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVAZ_MZ4_ZA_W1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 2)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 4
  let esize : Nat := 32
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Nat := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVAZ_MZ4_ZA_W1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_MZ4_ZA_W1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_MZ4_ZA_W1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_MZ4_ZA_W1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_MZ4_ZA_W1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVAZ_MZ4_ZA_D1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 4
  let esize : Nat := 64
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Nat := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVAZ_MZ4_ZA_D1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_MZ4_ZA_D1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_MZ4_ZA_D1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_MZ4_ZA_D1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_MZ4_ZA_D1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVAZ_MZ_ZA2_1 (Rv : (BitVec 2)) (off3 : (BitVec 3)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat off3)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_MOVAZ_MZ_ZA2_1 128 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_MOVAZ_MZ_ZA2_1 256 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_MOVAZ_MZ_ZA2_1 512 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_MOVAZ_MZ_ZA2_1 1024 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_MOVAZ_MZ_ZA2_1 2048 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_MOVAZ_MZ_ZA4_1 (Rv : (BitVec 2)) (off3 : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat off3)
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_MOVAZ_MZ_ZA4_1 128 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_MOVAZ_MZ_ZA4_1 256 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_MOVAZ_MZ_ZA4_1 512 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_MOVAZ_MZ_ZA4_1 1024 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_MOVAZ_MZ_ZA4_1 2048 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


/-- Type quantifiers: pc : Int -/
def __DecodeA64_SME__seg13 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__913 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                 __opcode 15 5)) == (0b10101000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 __opcode 1 0)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
    then
      (do
        let w__912 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__912 <b 2650) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__913 : Bool)
  then
    (do
      writeReg SEE 2650
      let size := (BitVec.slice __opcode 22 2)
      let Zm := (BitVec.slice __opcode 16 4)
      let Zdn := (BitVec.slice __opcode 2 3)
      let U := (BitVec.slice __opcode 0 1)
      (decode_UMAX_MZ_ZZV_4x1 size Zm Zdn U)
      (pure false))
  else
    (do
      let w__915 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                     __opcode 15 5)) == (0b10101000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     __opcode 1 0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
        then
          (do
            let w__914 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__914 <b 2651) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__915 : Bool)
      then
        (do
          writeReg SEE 2651
          let size := (BitVec.slice __opcode 22 2)
          let Zm := (BitVec.slice __opcode 16 4)
          let Zdn := (BitVec.slice __opcode 2 3)
          let U := (BitVec.slice __opcode 0 1)
          (decode_SMAX_MZ_ZZV_4x1 size Zm Zdn U)
          (pure false))
      else
        (do
          let w__917 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                         __opcode 16 5)) == (0x581#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 0 0)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
            then
              (do
                let w__916 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__916 <b 2652) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__917 : Bool)
          then
            (do
              writeReg SEE 2652
              let size := (BitVec.slice __opcode 22 2)
              let Zm := (BitVec.slice __opcode 17 4)
              let Zdn := (BitVec.slice __opcode 1 4)
              let U := (BitVec.slice __opcode 0 1)
              (decode_UMIN_MZ_ZZW_2x2 size Zm Zdn U)
              (pure false))
          else
            (do
              let w__919 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                             __opcode 16 5)) == (0x581#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 0 0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                then
                  (do
                    let w__918 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__918 <b 2653) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__919 : Bool)
              then
                (do
                  writeReg SEE 2653
                  let size := (BitVec.slice __opcode 22 2)
                  let Zm := (BitVec.slice __opcode 17 4)
                  let Zdn := (BitVec.slice __opcode 1 4)
                  let U := (BitVec.slice __opcode 0 1)
                  (decode_SMIN_MZ_ZZW_2x2 size Zm Zdn U)
                  (pure false))
              else
                (do
                  let w__921 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                 __opcode 15 5)) == (0b10100000001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 0 0)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                    then
                      (do
                        let w__920 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__920 <b 2654) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__921 : Bool)
                  then
                    (do
                      writeReg SEE 2654
                      let size := (BitVec.slice __opcode 22 2)
                      let Zm := (BitVec.slice __opcode 16 4)
                      let Zdn := (BitVec.slice __opcode 1 4)
                      let U := (BitVec.slice __opcode 0 1)
                      (decode_UMIN_MZ_ZZV_2x1 size Zm Zdn U)
                      (pure false))
                  else
                    (do
                      let w__923 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                     __opcode 15 5)) == (0b10100000001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 0 0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                        then
                          (do
                            let w__922 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__922 <b 2655) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__923 : Bool)
                      then
                        (do
                          writeReg SEE 2655
                          let size := (BitVec.slice __opcode 22 2)
                          let Zm := (BitVec.slice __opcode 16 4)
                          let Zdn := (BitVec.slice __opcode 1 4)
                          let U := (BitVec.slice __opcode 0 1)
                          (decode_SMIN_MZ_ZZV_2x1 size Zm Zdn U)
                          (pure false))
                      else
                        (do
                          let w__925 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                         __opcode 17 5)) == (0b0010111000001#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         __opcode 1 0)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                            then
                              (do
                                let w__924 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__924 <b 2656) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__925 : Bool)
                          then
                            (do
                              writeReg SEE 2656
                              let size := (BitVec.slice __opcode 22 2)
                              let Zm := (BitVec.slice __opcode 18 3)
                              let Zdn := (BitVec.slice __opcode 2 3)
                              let U := (BitVec.slice __opcode 0 1)
                              (decode_UMIN_MZ_ZZW_4x4 size Zm Zdn U)
                              (pure false))
                          else
                            (do
                              let w__927 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                             __opcode 17 5)) == (0b0010111000001#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                             __opcode 1 0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__926 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__926 <b 2657) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__927 : Bool)
                              then
                                (do
                                  writeReg SEE 2657
                                  let size := (BitVec.slice __opcode 22 2)
                                  let Zm := (BitVec.slice __opcode 18 3)
                                  let Zdn := (BitVec.slice __opcode 2 3)
                                  let U := (BitVec.slice __opcode 0 1)
                                  (decode_SMIN_MZ_ZZW_4x4 size Zm Zdn U)
                                  (pure false))
                              else
                                (do
                                  let w__929 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 15 5)) == (0b10101000001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                 __opcode 1 0)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__928 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__928 <b 2658) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__929 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2658
                                      let size := (BitVec.slice __opcode 22 2)
                                      let Zm := (BitVec.slice __opcode 16 4)
                                      let Zdn := (BitVec.slice __opcode 2 3)
                                      let U := (BitVec.slice __opcode 0 1)
                                      (decode_UMIN_MZ_ZZV_4x1 size Zm Zdn U)
                                      (pure false))
                                  else
                                    (do
                                      let w__931 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                     __opcode 15 5)) == (0b10101000001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                     __opcode 1 0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__930 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__930 <b 2659) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__931 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2659
                                          let size := (BitVec.slice __opcode 22 2)
                                          let Zm := (BitVec.slice __opcode 16 4)
                                          let Zdn := (BitVec.slice __opcode 2 3)
                                          let U := (BitVec.slice __opcode 0 1)
                                          (decode_SMIN_MZ_ZZV_4x1 size Zm Zdn U)
                                          (pure false))
                                      else
                                        (do
                                          let w__933 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 16 5)) == (0x591#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 0 0)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__932 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__932 <b 2660) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__933 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2660
                                              let size := (BitVec.slice __opcode 22 2)
                                              let Zm := (BitVec.slice __opcode 17 4)
                                              let Zdn := (BitVec.slice __opcode 1 4)
                                              let U := (BitVec.slice __opcode 0 1)
                                              (decode_URSHL_MZ_ZZW_2x2 size Zm Zdn U)
                                              (pure false))
                                          else
                                            (do
                                              let w__935 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 16 5)) == (0x591#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 0 0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__934 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__934 <b 2661) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__935 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2661
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let Zm := (BitVec.slice __opcode 17 4)
                                                  let Zdn := (BitVec.slice __opcode 1 4)
                                                  let U := (BitVec.slice __opcode 0 1)
                                                  (decode_SRSHL_MZ_ZZW_2x2 size Zm Zdn U)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__937 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 15 5)) == (0b10100010001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 0 0)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__936 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__936 <b 2662) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__937 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2662
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let Zm := (BitVec.slice __opcode 16 4)
                                                      let Zdn := (BitVec.slice __opcode 1 4)
                                                      let U := (BitVec.slice __opcode 0 1)
                                                      (decode_URSHL_MZ_ZZV_2x1 size Zm Zdn U)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__939 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 15 5)) == (0b10100010001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 0 0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__938 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__938 <b 2663) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__939 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2663
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let Zm := (BitVec.slice __opcode 16 4)
                                                          let Zdn := (BitVec.slice __opcode 1 4)
                                                          let U := (BitVec.slice __opcode 0 1)
                                                          (decode_SRSHL_MZ_ZZV_2x1 size Zm Zdn U)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__941 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                         __opcode 17 5)) == (0b0010111010001#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                         __opcode 1 0)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__940 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__940 <b 2664) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__941 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2664
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let Zm := (BitVec.slice __opcode 18 3)
                                                              let Zdn := (BitVec.slice __opcode 2 3)
                                                              let U := (BitVec.slice __opcode 0 1)
                                                              (decode_URSHL_MZ_ZZW_4x4 size Zm Zdn U)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__943 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                             __opcode 17 5)) == (0b0010111010001#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                             __opcode 1 0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__942 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__942 <b 2665) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__943 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2665
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 18 3)
                                                                  let Zdn :=
                                                                    (BitVec.slice __opcode 2 3)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 0 1)
                                                                  (decode_SRSHL_MZ_ZZW_4x4 size Zm
                                                                    Zdn U)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__945 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 5)) == (0b10101010001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                 __opcode 1 0)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__944 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__944 <b 2666) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__945 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2666
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Zdn :=
                                                                        (BitVec.slice __opcode 2 3)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 0 1)
                                                                      (decode_URSHL_MZ_ZZV_4x1 size
                                                                        Zm Zdn U)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__947 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 5)) == (0b10101010001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                     __opcode 1 0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__946 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__946 <b 2667) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__947 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2667
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Zdn :=
                                                                            (BitVec.slice __opcode 2
                                                                              3)
                                                                          let U :=
                                                                            (BitVec.slice __opcode 0
                                                                              1)
                                                                          (decode_SRSHL_MZ_ZZV_4x1
                                                                            size Zm Zdn U)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__949 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 16
                                                                                         5)) == (0x5A0#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 0
                                                                                         0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__948 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__948 <b 2668) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__949 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2668
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 17 4)
                                                                              let Zdn :=
                                                                                (BitVec.slice
                                                                                  __opcode 1 4)
                                                                              (decode_SQDMULH_MZ_ZZW_2x2
                                                                                size Zm Zdn)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__951 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 5)) == (0b10100100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             0 0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__950 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__950 <b 2669) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__951 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2669
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Zdn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 1 4)
                                                                                  (decode_SQDMULH_MZ_ZZV_2x1
                                                                                    size Zm Zdn)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__953 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 17
                                                                                                 5)) == (0b0010111100000#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 1 0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__952 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__952 <b 2670) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__953 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2670
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          18 3)
                                                                                      let Zdn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 2
                                                                                          3)
                                                                                      (decode_SQDMULH_MZ_ZZW_4x4
                                                                                        size Zm Zdn)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__955 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     5)) == (0b10101100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     1
                                                                                                     0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__954 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__954 <b 2671) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__955 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2671
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Zdn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              2 3)
                                                                                          (decode_SQDMULH_MZ_ZZV_4x1
                                                                                            size Zm
                                                                                            Zdn)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__957 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         5)) == (0b10100011000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         0
                                                                                                         0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__956 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__956 <b 2672) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__957 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2672
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Zdn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  1
                                                                                                  4)
                                                                                              (decode_ADD_MZ_ZZV_2x1
                                                                                                size
                                                                                                Zm
                                                                                                Zdn)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__959 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             5)) == (0b10101011000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             1
                                                                                                             0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__958 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__958 <b 2673) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__959 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2673
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      2)
                                                                                                  let Zm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Zdn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      2
                                                                                                      3)
                                                                                                  (decode_ADD_MZ_ZZV_4x1
                                                                                                    size
                                                                                                    Zm
                                                                                                    Zdn)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__961 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 10)) == (0b110001#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 0
                                                                                                                 0)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__960 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__960 <b 2674) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__961 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2674
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          2)
                                                                                                      let Zm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          5)
                                                                                                      let Zn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let Zd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          1
                                                                                                          4)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          1)
                                                                                                      (decode_UCLAMP_MZ_ZZ_2
                                                                                                        size
                                                                                                        Zm
                                                                                                        Zn
                                                                                                        Zd
                                                                                                        U)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__963 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     10)) == (0b110001#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     0
                                                                                                                     0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__962 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__962 <b 2675) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__963 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2675
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              2)
                                                                                                          let Zm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let Zn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let Zd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              1
                                                                                                              4)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              1)
                                                                                                          (decode_SCLAMP_MZ_ZZ_2
                                                                                                            size
                                                                                                            Zm
                                                                                                            Zn
                                                                                                            Zd
                                                                                                            U)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__965 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         10)) == (0b110011#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         1
                                                                                                                         0)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__964 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__964 <b 2676) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__965 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2676
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
                                                                                                              let Zm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
                                                                                                              let Zn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let Zd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  2
                                                                                                                  3)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  1)
                                                                                                              (decode_UCLAMP_MZ_ZZ_4
                                                                                                                size
                                                                                                                Zm
                                                                                                                Zn
                                                                                                                Zd
                                                                                                                U)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__967 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             10)) == (0b110011#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             1
                                                                                                                             0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__966 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__966 <b 2677) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__967 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2677
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
                                                                                                                  let Zm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let Zn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let Zd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      2
                                                                                                                      3)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      1)
                                                                                                                  (decode_SCLAMP_MZ_ZZ_4
                                                                                                                    size
                                                                                                                    Zm
                                                                                                                    Zn
                                                                                                                    Zd
                                                                                                                    U)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__969 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               10)) == (0x978#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               0
                                                                                                                               0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__968 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__968 <b 2678) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__969 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2678
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let Zn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let Zd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          1
                                                                                                                          4)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          1)
                                                                                                                      (decode_UUNPK_MZ_Z_2
                                                                                                                        size
                                                                                                                        Zn
                                                                                                                        Zd
                                                                                                                        U)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__971 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   10)) == (0x978#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   0
                                                                                                                                   0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__970 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__970 <b 2679) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__971 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2679
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let Zn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let Zd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              1
                                                                                                                              4)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              1)
                                                                                                                          (decode_SUNPK_MZ_Z_2
                                                                                                                            size
                                                                                                                            Zn
                                                                                                                            Zd
                                                                                                                            U)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__973 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       10)) == (0xD78#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         5
                                                                                                                                         5)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         1
                                                                                                                                         0)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__972 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__972 <b 2680) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__973 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2680
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let Zn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  6
                                                                                                                                  4)
                                                                                                                              let Zd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  2
                                                                                                                                  3)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  1)
                                                                                                                              (decode_UUNPK_MZ_Z_4
                                                                                                                                size
                                                                                                                                Zn
                                                                                                                                Zd
                                                                                                                                U)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__975 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           10)) == (0xD78#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             5
                                                                                                                                             5)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             1
                                                                                                                                             0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__974 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__974 <b 2681) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__975 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2681
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let Zn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      6
                                                                                                                                      4)
                                                                                                                                  let Zd :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      2
                                                                                                                                      3)
                                                                                                                                  let U :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      1)
                                                                                                                                  (decode_SUNPK_MZ_Z_4
                                                                                                                                    size
                                                                                                                                    Zn
                                                                                                                                    Zd
                                                                                                                                    U)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__977 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             20)) == (0xC1E#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               10)) == (0b110101#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               5
                                                                                                                                               5)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__976 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__976 <b 2682) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__977 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2682
                                                                                                                                      let imm4 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
                                                                                                                                      let Zn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          6
                                                                                                                                          4)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          1)
                                                                                                                                      let Zd :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      (decode_SQRSHR_Z_MZ2__
                                                                                                                                        imm4
                                                                                                                                        Zn
                                                                                                                                        U
                                                                                                                                        Zd)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__979 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 20)) == (0xC1E#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   10)) == (0b110101#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   5
                                                                                                                                                   5)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__978 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__978 <b 2683) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__979 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2683
                                                                                                                                          let imm4 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let Zn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              6
                                                                                                                                              4)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              1)
                                                                                                                                          let Zd :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_UQRSHR_Z_MZ2__
                                                                                                                                            imm4
                                                                                                                                            Zn
                                                                                                                                            U
                                                                                                                                            Zd)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__981 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     20)) == (0xC1F#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       10)) == (0b110101#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       5
                                                                                                                                                       5)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__980 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__980 <b 2684) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__981 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2684
                                                                                                                                              let imm4 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  4)
                                                                                                                                              let Zn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  6
                                                                                                                                                  4)
                                                                                                                                              let U :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  1)
                                                                                                                                              let Zd :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              (decode_SQRSHRU_Z_MZ2__
                                                                                                                                                imm4
                                                                                                                                                Zn
                                                                                                                                                U
                                                                                                                                                Zd)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__983 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           21
                                                                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             10)) == (0b110111#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             6
                                                                                                                                                             5)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__982 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__982 <b 2685) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__983 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2685
                                                                                                                                                  let tsize :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      2)
                                                                                                                                                  let imm5 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      5)
                                                                                                                                                  let N :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      10
                                                                                                                                                      1)
                                                                                                                                                  let Zn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      7
                                                                                                                                                      3)
                                                                                                                                                  let U :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      1)
                                                                                                                                                  let Zd :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_SQRSHRN_Z_MZ4__
                                                                                                                                                    tsize
                                                                                                                                                    imm5
                                                                                                                                                    N
                                                                                                                                                    Zn
                                                                                                                                                    U
                                                                                                                                                    Zd)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__985 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               21
                                                                                                                                                               21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 15
                                                                                                                                                                 10)) == (0b110111#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 6
                                                                                                                                                                 5)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__984 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__984 <b 2686) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__985 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 2686
                                                                                                                                                      let tsize :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          2)
                                                                                                                                                      let imm5 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          5)
                                                                                                                                                      let N :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          10
                                                                                                                                                          1)
                                                                                                                                                      let Zn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          7
                                                                                                                                                          3)
                                                                                                                                                      let U :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          1)
                                                                                                                                                      let Zd :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_UQRSHRN_Z_MZ4__
                                                                                                                                                        tsize
                                                                                                                                                        imm5
                                                                                                                                                        N
                                                                                                                                                        Zn
                                                                                                                                                        U
                                                                                                                                                        Zd)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__987 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   21
                                                                                                                                                                   21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     15
                                                                                                                                                                     10)) == (0b110111#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     6
                                                                                                                                                                     5)) == (0b10#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__986 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__986 <b 2687) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__987 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 2687
                                                                                                                                                          let tsize :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              2)
                                                                                                                                                          let imm5 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              5)
                                                                                                                                                          let N :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              1)
                                                                                                                                                          let Zn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              7
                                                                                                                                                              3)
                                                                                                                                                          let U :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              1)
                                                                                                                                                          let Zd :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          (decode_SQRSHRUN_Z_MZ4__
                                                                                                                                                            tsize
                                                                                                                                                            imm5
                                                                                                                                                            N
                                                                                                                                                            Zn
                                                                                                                                                            U
                                                                                                                                                            Zd)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__989 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       21
                                                                                                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         15
                                                                                                                                                                         10)) == (0b110110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         6
                                                                                                                                                                         5)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__988 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__988 <b 2688) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__989 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 2688
                                                                                                                                                              let tsize :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  22
                                                                                                                                                                  2)
                                                                                                                                                              let imm5 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  5)
                                                                                                                                                              let N :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  10
                                                                                                                                                                  1)
                                                                                                                                                              let Zn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  7
                                                                                                                                                                  3)
                                                                                                                                                              let U :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  1)
                                                                                                                                                              let Zd :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  5)
                                                                                                                                                              (decode_SQRSHR_Z_MZ4__
                                                                                                                                                                tsize
                                                                                                                                                                imm5
                                                                                                                                                                N
                                                                                                                                                                Zn
                                                                                                                                                                U
                                                                                                                                                                Zd)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__991 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           21
                                                                                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             15
                                                                                                                                                                             10)) == (0b110110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             6
                                                                                                                                                                             5)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__990 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__990 <b 2689) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__991 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 2689
                                                                                                                                                                  let tsize :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      2)
                                                                                                                                                                  let imm5 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      5)
                                                                                                                                                                  let N :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      10
                                                                                                                                                                      1)
                                                                                                                                                                  let Zn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      7
                                                                                                                                                                      3)
                                                                                                                                                                  let U :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      5
                                                                                                                                                                      1)
                                                                                                                                                                  let Zd :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      5)
                                                                                                                                                                  (decode_UQRSHR_Z_MZ4__
                                                                                                                                                                    tsize
                                                                                                                                                                    imm5
                                                                                                                                                                    N
                                                                                                                                                                    Zn
                                                                                                                                                                    U
                                                                                                                                                                    Zd)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
