import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0988
import ArmFull.Fn.M0989
import ArmFull.Fn.M0990
import ArmFull.Fn.M1135
import ArmFull.Fn.M1136
import ArmFull.Fn.M1141

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

def decode_BFMAXNM_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFMAXNM_MZ_ZZW_4x4 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMAXNM_MZ_ZZW_4x4 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMAXNM_MZ_ZZW_4x4 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMAXNM_MZ_ZZW_4x4 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMAXNM_MZ_ZZW_4x4 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMAXNM_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFMAXNM_MZ_ZZV_4x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMAXNM_MZ_ZZV_4x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMAXNM_MZ_ZZV_4x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMAXNM_MZ_ZZV_4x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMAXNM_MZ_ZZV_4x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMINNM_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFMINNM_MZ_ZZW_4x4 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMINNM_MZ_ZZW_4x4 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMINNM_MZ_ZZW_4x4 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMINNM_MZ_ZZW_4x4 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMINNM_MZ_ZZW_4x4 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_BFMINNM_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFMINNM_MZ_ZZV_4x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 256 =>
    (do
      (execute_BFMINNM_MZ_ZZV_4x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 512 =>
    (do
      (execute_BFMINNM_MZ_ZZV_4x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 1024 =>
    (do
      (execute_BFMINNM_MZ_ZZV_4x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | 2048 =>
    (do
      (execute_BFMINNM_MZ_ZZV_4x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m)) nreg))
  | _ => (pure (()))


def decode_FCVT_MZ2_Z__ (Zn : (BitVec 5)) (Zd : (BitVec 4)) (L : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF16F16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  match VL with
  | 128 =>
    (do
      (execute_FCVT_MZ2_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FCVT_MZ2_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FCVT_MZ2_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FCVT_MZ2_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FCVT_MZ2_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FCVTL_MZ2_Z__ (Zn : (BitVec 5)) (Zd : (BitVec 4)) (L : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF16F16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  match VL with
  | 128 =>
    (do
      (execute_FCVTL_MZ2_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FCVTL_MZ2_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FCVTL_MZ2_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FCVTL_MZ2_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FCVTL_MZ2_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFCLAMP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFCLAMP_MZ_ZZ_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_BFCLAMP_MZ_ZZ_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_BFCLAMP_MZ_ZZ_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_BFCLAMP_MZ_ZZ_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_BFCLAMP_MZ_ZZ_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_BFCLAMP_MZ_ZZ_4 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFCLAMP_MZ_ZZ_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_BFCLAMP_MZ_ZZ_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_BFCLAMP_MZ_ZZ_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_BFCLAMP_MZ_ZZ_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_BFCLAMP_MZ_ZZ_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


/-- Type quantifiers: pc : Int -/
def __DecodeA64_SME__seg8 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__587 ← (( do
    if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b1100000100100010111000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 5 5)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
    then
      (do
        let w__586 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__586 <b 2487) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__587 : Bool)
  then
    (do
      writeReg SEE 2487
      let Zn := (BitVec.slice __opcode 6 4)
      let U := (BitVec.slice __opcode 5 1)
      let Zd := (BitVec.slice __opcode 1 4)
      (decode_SCVTF_MZ_Z_2 Zn U Zd)
      (pure false))
  else
    (do
      let w__589 ← (( do
        if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b1100000100110010111000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 6 5)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
        then
          (do
            let w__588 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__588 <b 2488) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__589 : Bool)
      then
        (do
          writeReg SEE 2488
          let Zn := (BitVec.slice __opcode 7 3)
          let U := (BitVec.slice __opcode 5 1)
          let Zd := (BitVec.slice __opcode 2 3)
          (decode_SCVTF_MZ_Z_4 Zn U Zd)
          (pure false))
      else
        (do
          let w__591 ← (( do
            if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b1100000110101100111000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 5 5)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
            then
              (do
                let w__590 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__590 <b 2489) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__591 : Bool)
          then
            (do
              writeReg SEE 2489
              let size := (BitVec.slice __opcode 22 2)
              let Zn := (BitVec.slice __opcode 6 4)
              let Zd := (BitVec.slice __opcode 1 4)
              (decode_FRINTA_MZ_Z_2 size Zn Zd)
              (pure false))
          else
            (do
              let w__593 ← (( do
                if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b1100000110101010111000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 5 5)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    let w__592 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__592 <b 2490) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__593 : Bool)
              then
                (do
                  writeReg SEE 2490
                  let size := (BitVec.slice __opcode 22 2)
                  let Zn := (BitVec.slice __opcode 6 4)
                  let Zd := (BitVec.slice __opcode 1 4)
                  (decode_FRINTM_MZ_Z_2 size Zn Zd)
                  (pure false))
              else
                (do
                  let w__595 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b1100000110101000111000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 5 5)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                    then
                      (do
                        let w__594 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__594 <b 2491) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__595 : Bool)
                  then
                    (do
                      writeReg SEE 2491
                      let size := (BitVec.slice __opcode 22 2)
                      let Zn := (BitVec.slice __opcode 6 4)
                      let Zd := (BitVec.slice __opcode 1 4)
                      (decode_FRINTN_MZ_Z_2 size Zn Zd)
                      (pure false))
                  else
                    (do
                      let w__597 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31
                                 10)) == (0b1100000110101001111000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 5 5)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                        then
                          (do
                            let w__596 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__596 <b 2492) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__597 : Bool)
                      then
                        (do
                          writeReg SEE 2492
                          let size := (BitVec.slice __opcode 22 2)
                          let Zn := (BitVec.slice __opcode 6 4)
                          let Zd := (BitVec.slice __opcode 1 4)
                          (decode_FRINTP_MZ_Z_2 size Zn Zd)
                          (pure false))
                      else
                        (do
                          let w__599 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode
                                     31 10)) == (0b1100000110111100111000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 6 5)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                            then
                              (do
                                let w__598 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__598 <b 2493) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__599 : Bool)
                          then
                            (do
                              writeReg SEE 2493
                              let size := (BitVec.slice __opcode 22 2)
                              let Zn := (BitVec.slice __opcode 7 3)
                              let Zd := (BitVec.slice __opcode 2 3)
                              (decode_FRINTA_MZ_Z_4 size Zn Zd)
                              (pure false))
                          else
                            (do
                              let w__601 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                         __opcode 31 10)) == (0b1100000110111010111000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 6 5)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__600 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__600 <b 2494) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__601 : Bool)
                              then
                                (do
                                  writeReg SEE 2494
                                  let size := (BitVec.slice __opcode 22 2)
                                  let Zn := (BitVec.slice __opcode 7 3)
                                  let Zd := (BitVec.slice __opcode 2 3)
                                  (decode_FRINTM_MZ_Z_4 size Zn Zd)
                                  (pure false))
                              else
                                (do
                                  let w__603 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                             __opcode 31 10)) == (0b1100000110111000111000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 6 5)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__602 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__602 <b 2495) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__603 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2495
                                      let size := (BitVec.slice __opcode 22 2)
                                      let Zn := (BitVec.slice __opcode 7 3)
                                      let Zd := (BitVec.slice __opcode 2 3)
                                      (decode_FRINTN_MZ_Z_4 size Zn Zd)
                                      (pure false))
                                  else
                                    (do
                                      let w__605 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                 __opcode 31 10)) == (0b1100000110111001111000#22 : (BitVec 22))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 6 5)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__604 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__604 <b 2496) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__605 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2496
                                          let size := (BitVec.slice __opcode 22 2)
                                          let Zn := (BitVec.slice __opcode 7 3)
                                          let Zd := (BitVec.slice __opcode 2 3)
                                          (decode_FRINTP_MZ_Z_4 size Zn Zd)
                                          (pure false))
                                      else
                                        (do
                                          let w__607 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                       __opcode 21 15)) == (0b1000000#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 12 10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 5 3)) == (0b010#3 : (BitVec 3)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__606 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__606 <b 2497) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__607 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2497
                                              let sz := (BitVec.slice __opcode 22 1)
                                              let Rv := (BitVec.slice __opcode 13 2)
                                              let Zm := (BitVec.slice __opcode 6 4)
                                              let S := (BitVec.slice __opcode 3 1)
                                              let off3 := (BitVec.slice __opcode 0 3)
                                              (decode_ADD_ZA_ZW_2x2 sz Rv Zm S off3)
                                              (pure false))
                                          else
                                            (do
                                              let w__609 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                           __opcode 21 15)) == (0b1000000#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 12 10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 5 3)) == (0b011#3 : (BitVec 3)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__608 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__608 <b 2498) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__609 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2498
                                                  let sz := (BitVec.slice __opcode 22 1)
                                                  let Rv := (BitVec.slice __opcode 13 2)
                                                  let Zm := (BitVec.slice __opcode 6 4)
                                                  let S := (BitVec.slice __opcode 3 1)
                                                  let off3 := (BitVec.slice __opcode 0 3)
                                                  (decode_SUB_ZA_ZW_2x2 sz Rv Zm S off3)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__611 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                               __opcode 21 15)) == (0b1000010#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 12 10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                 __opcode 6 3)) == (0x2#4 : (BitVec 4)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__610 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__610 <b 2499) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__611 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2499
                                                      let sz := (BitVec.slice __opcode 22 1)
                                                      let Rv := (BitVec.slice __opcode 13 2)
                                                      let Zm := (BitVec.slice __opcode 7 3)
                                                      let S := (BitVec.slice __opcode 3 1)
                                                      let off3 := (BitVec.slice __opcode 0 3)
                                                      (decode_ADD_ZA_ZW_4x4 sz Rv Zm S off3)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__613 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                   __opcode 21 15)) == (0b1000010#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 12 10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 6 3)) == (0x3#4 : (BitVec 4)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__612 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__612 <b 2500) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__613 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2500
                                                          let sz := (BitVec.slice __opcode 22 1)
                                                          let Rv := (BitVec.slice __opcode 13 2)
                                                          let Zm := (BitVec.slice __opcode 7 3)
                                                          let S := (BitVec.slice __opcode 3 1)
                                                          let off3 := (BitVec.slice __opcode 0 3)
                                                          (decode_SUB_ZA_ZW_4x4 sz Rv Zm S off3)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__615 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                         __opcode 16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 12 10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 5 3)) == (0b010#3 : (BitVec 3))))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__614 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__614 <b 2501) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__615 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2501
                                                              let sz := (BitVec.slice __opcode 22 1)
                                                              let Zm := (BitVec.slice __opcode 17 4)
                                                              let Rv := (BitVec.slice __opcode 13 2)
                                                              let Zn := (BitVec.slice __opcode 6 4)
                                                              let S := (BitVec.slice __opcode 3 1)
                                                              let off3 :=
                                                                (BitVec.slice __opcode 0 3)
                                                              (decode_ADD_ZA_ZZW_2x2 sz Zm Rv Zn S
                                                                off3)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__617 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                             __opcode 16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 12 10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 5 3)) == (0b011#3 : (BitVec 3))))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__616 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__616 <b 2502) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__617 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2502
                                                                  let sz :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 17 4)
                                                                  let Rv :=
                                                                    (BitVec.slice __opcode 13 2)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 6 4)
                                                                  let S :=
                                                                    (BitVec.slice __opcode 3 1)
                                                                  let off3 :=
                                                                    (BitVec.slice __opcode 0 3)
                                                                  (decode_SUB_ZA_ZZW_2x2 sz Zm Rv Zn
                                                                    S off3)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__619 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                   __opcode 12 10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 4 3)) == (0b10#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__618 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__618 <b 2503) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__619 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2503
                                                                      let sz :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rv :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 3 1)
                                                                      let off3 :=
                                                                        (BitVec.slice __opcode 0 3)
                                                                      (decode_ADD_ZA_ZZV_2x1 sz Zm
                                                                        Rv Zn S off3)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__621 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                       __opcode 12
                                                                                       10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 4 3)) == (0b11#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__620 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__620 <b 2504) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__621 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2504
                                                                          let sz :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Rv :=
                                                                            (BitVec.slice __opcode
                                                                              13 2)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let S :=
                                                                            (BitVec.slice __opcode 3
                                                                              1)
                                                                          let off3 :=
                                                                            (BitVec.slice __opcode 0
                                                                              3)
                                                                          (decode_SUB_ZA_ZZV_2x1 sz
                                                                            Zm Rv Zn S off3)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__623 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                         __opcode 17
                                                                                         15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           12 10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           6 3)) == (0x2#4 : (BitVec 4))))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__622 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__622 <b 2505) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__623 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2505
                                                                              let sz :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 18 3)
                                                                              let Rv :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 2)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 7 3)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 3 1)
                                                                              let off3 :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 3)
                                                                              (decode_ADD_ZA_ZZW_4x4
                                                                                sz Zm Rv Zn S off3)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__625 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               12 10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               6 3)) == (0x3#4 : (BitVec 4))))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__624 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__624 <b 2506) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__625 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2506
                                                                                  let sz :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 18 3)
                                                                                  let Rv :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 2)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 7 3)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 3 1)
                                                                                  let off3 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 3)
                                                                                  (decode_SUB_ZA_ZZW_4x4
                                                                                    sz Zm Rv Zn S
                                                                                    off3)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__627 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   12
                                                                                                   10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   4
                                                                                                   3)) == (0b10#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__626 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__626 <b 2507) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__627 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2507
                                                                                      let sz :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rv :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 2)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode 3
                                                                                          1)
                                                                                      let off3 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          3)
                                                                                      (decode_ADD_ZA_ZZV_4x1
                                                                                        sz Zm Rv Zn
                                                                                        S off3)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__629 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       12
                                                                                                       10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       4
                                                                                                       3)) == (0b11#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__628 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__628 <b 2508) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__629 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2508
                                                                                          let sz :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rv :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 2)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              3 1)
                                                                                          let off3 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 3)
                                                                                          (decode_SUB_ZA_ZZV_4x1
                                                                                            sz Zm Rv
                                                                                            Zn S
                                                                                            off3)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__631 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         16
                                                                                                         15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           12
                                                                                                           10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           5
                                                                                                           3)) == (0b010#3 : (BitVec 3))))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__630 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__630 <b 2509) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__631 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2509
                                                                                              let sz :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  17
                                                                                                  4)
                                                                                              let Rv :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  2)
                                                                                              let Zn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  6
                                                                                                  4)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  4
                                                                                                  1)
                                                                                              let off3 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  3)
                                                                                              (decode_UDOT_ZA_ZZW_2x2
                                                                                                sz
                                                                                                Zm
                                                                                                Rv
                                                                                                Zn U
                                                                                                off3)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__633 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             16
                                                                                                             15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               12
                                                                                                               10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               5
                                                                                                               3)) == (0b000#3 : (BitVec 3))))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__632 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__632 <b 2510) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__633 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2510
                                                                                                  let sz :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let Zm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      17
                                                                                                      4)
                                                                                                  let Rv :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      13
                                                                                                      2)
                                                                                                  let Zn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      6
                                                                                                      4)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      4
                                                                                                      1)
                                                                                                  let off3 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      3)
                                                                                                  (decode_SDOT_ZA_ZZW_2x2
                                                                                                    sz
                                                                                                    Zm
                                                                                                    Rv
                                                                                                    Zn
                                                                                                    U
                                                                                                    off3)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__635 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               16
                                                                                                               15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 12
                                                                                                                 10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 5
                                                                                                                 3)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__634 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__634 <b 2511) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__635 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2511
                                                                                                      let Zm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          17
                                                                                                          4)
                                                                                                      let Rv :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          2)
                                                                                                      let Zn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          6
                                                                                                          4)
                                                                                                      let off3 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          3)
                                                                                                      (decode_USDOT_ZA_ZZW_S2x2
                                                                                                        Zm
                                                                                                        Rv
                                                                                                        Zn
                                                                                                        off3)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__637 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       12
                                                                                                                       10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       4
                                                                                                                       3)) == (0b10#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__636 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__636 <b 2512) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__637 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2512
                                                                                                          let sz :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let Zm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let Rv :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              2)
                                                                                                          let Zn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              4
                                                                                                              1)
                                                                                                          let off3 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              3)
                                                                                                          (decode_UDOT_ZA_ZZV_2x1
                                                                                                            sz
                                                                                                            Zm
                                                                                                            Rv
                                                                                                            Zn
                                                                                                            U
                                                                                                            off3)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__639 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           12
                                                                                                                           10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           4
                                                                                                                           3)) == (0b00#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__638 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__638 <b 2513) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__639 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2513
                                                                                                              let sz :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let Zm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let Rv :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  2)
                                                                                                              let Zn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  4
                                                                                                                  1)
                                                                                                              let off3 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  3)
                                                                                                              (decode_SDOT_ZA_ZZV_2x1
                                                                                                                sz
                                                                                                                Zm
                                                                                                                Rv
                                                                                                                Zn
                                                                                                                U
                                                                                                                off3)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__641 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             12
                                                                                                                             10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             4
                                                                                                                             3)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__640 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__640 <b 2514) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__641 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2514
                                                                                                                  let Zm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let Rv :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      2)
                                                                                                                  let Zn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      4
                                                                                                                      1)
                                                                                                                  let off3 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      3)
                                                                                                                  (decode_USDOT_ZA_ZZV_S2x1
                                                                                                                    Zm
                                                                                                                    Rv
                                                                                                                    Zn
                                                                                                                    U
                                                                                                                    off3)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__643 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 12
                                                                                                                                 10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 4
                                                                                                                                 3)) == (0b11#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__642 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__642 <b 2515) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__643 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2515
                                                                                                                      let Zm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let Rv :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          13
                                                                                                                          2)
                                                                                                                      let Zn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          4
                                                                                                                          1)
                                                                                                                      let off3 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          3)
                                                                                                                      (decode_SUDOT_ZA_ZZV_S2x1
                                                                                                                        Zm
                                                                                                                        Rv
                                                                                                                        Zn
                                                                                                                        U
                                                                                                                        off3)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__645 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     17
                                                                                                                                     15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       12
                                                                                                                                       10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       6
                                                                                                                                       3)) == (0x2#4 : (BitVec 4))))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__644 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__644 <b 2516) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__645 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2516
                                                                                                                          let sz :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              18
                                                                                                                              3)
                                                                                                                          let Rv :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              2)
                                                                                                                          let Zn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              7
                                                                                                                              3)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              4
                                                                                                                              1)
                                                                                                                          let off3 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              3)
                                                                                                                          (decode_UDOT_ZA_ZZW_4x4
                                                                                                                            sz
                                                                                                                            Zm
                                                                                                                            Rv
                                                                                                                            Zn
                                                                                                                            U
                                                                                                                            off3)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__647 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         17
                                                                                                                                         15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           12
                                                                                                                                           10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           6
                                                                                                                                           3)) == (0x0#4 : (BitVec 4))))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__646 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__646 <b 2517) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__647 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2517
                                                                                                                              let sz :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  1)
                                                                                                                              let Zm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  18
                                                                                                                                  3)
                                                                                                                              let Rv :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  13
                                                                                                                                  2)
                                                                                                                              let Zn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  7
                                                                                                                                  3)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  4
                                                                                                                                  1)
                                                                                                                              let off3 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  3)
                                                                                                                              (decode_SDOT_ZA_ZZW_4x4
                                                                                                                                sz
                                                                                                                                Zm
                                                                                                                                Rv
                                                                                                                                Zn
                                                                                                                                U
                                                                                                                                off3)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__649 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           17
                                                                                                                                           15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             12
                                                                                                                                             10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             6
                                                                                                                                             3)) == (0x1#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__648 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__648 <b 2518) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__649 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2518
                                                                                                                                  let Zm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      18
                                                                                                                                      3)
                                                                                                                                  let Rv :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      13
                                                                                                                                      2)
                                                                                                                                  let Zn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      7
                                                                                                                                      3)
                                                                                                                                  let off3 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      3)
                                                                                                                                  (decode_USDOT_ZA_ZZW_S4x4
                                                                                                                                    Zm
                                                                                                                                    Rv
                                                                                                                                    Zn
                                                                                                                                    off3)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__651 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   12
                                                                                                                                                   10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   4
                                                                                                                                                   3)) == (0b10#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__650 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__650 <b 2519) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__651 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2519
                                                                                                                                      let sz :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          1)
                                                                                                                                      let Zm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
                                                                                                                                      let Rv :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          13
                                                                                                                                          2)
                                                                                                                                      let Zn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          4
                                                                                                                                          1)
                                                                                                                                      let off3 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          3)
                                                                                                                                      (decode_UDOT_ZA_ZZV_4x1
                                                                                                                                        sz
                                                                                                                                        Zm
                                                                                                                                        Rv
                                                                                                                                        Zn
                                                                                                                                        U
                                                                                                                                        off3)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__653 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       12
                                                                                                                                                       10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       4
                                                                                                                                                       3)) == (0b00#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__652 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__652 <b 2520) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__653 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2520
                                                                                                                                          let sz :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              1)
                                                                                                                                          let Zm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let Rv :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              13
                                                                                                                                              2)
                                                                                                                                          let Zn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              4
                                                                                                                                              1)
                                                                                                                                          let off3 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              3)
                                                                                                                                          (decode_SDOT_ZA_ZZV_4x1
                                                                                                                                            sz
                                                                                                                                            Zm
                                                                                                                                            Rv
                                                                                                                                            Zn
                                                                                                                                            U
                                                                                                                                            off3)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__655 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     20)) == (0xC13#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         12
                                                                                                                                                         10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         4
                                                                                                                                                         3)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__654 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__654 <b 2521) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__655 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2521
                                                                                                                                              let Zm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  4)
                                                                                                                                              let Rv :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  13
                                                                                                                                                  2)
                                                                                                                                              let Zn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let U :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  4
                                                                                                                                                  1)
                                                                                                                                              let off3 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  3)
                                                                                                                                              (decode_USDOT_ZA_ZZV_S4x1
                                                                                                                                                Zm
                                                                                                                                                Rv
                                                                                                                                                Zn
                                                                                                                                                U
                                                                                                                                                off3)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__657 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         20)) == (0xC13#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           15
                                                                                                                                                           15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             12
                                                                                                                                                             10)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             4
                                                                                                                                                             3)) == (0b11#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__656 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__656 <b 2522) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__657 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2522
                                                                                                                                                  let Zm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      4)
                                                                                                                                                  let Rv :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      13
                                                                                                                                                      2)
                                                                                                                                                  let Zn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let U :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      4
                                                                                                                                                      1)
                                                                                                                                                  let off3 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      3)
                                                                                                                                                  (decode_SUDOT_ZA_ZZV_S4x1
                                                                                                                                                    Zm
                                                                                                                                                    Rv
                                                                                                                                                    Zn
                                                                                                                                                    U
                                                                                                                                                    off3)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
