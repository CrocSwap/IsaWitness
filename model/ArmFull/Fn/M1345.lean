import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M1163
import ArmFull.Fn.M1164
import ArmFull.Fn.M1166
import ArmFull.Fn.M1260
import ArmFull.Fn.M1261

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

def decode_STNT1H_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let tstride : Nat := 4
  let t : Int := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize : Nat := 16
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_STNT1H_MZx_P_BI_4x4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_STNT1H_MZx_P_BI_4x4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_STNT1H_MZx_P_BI_4x4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_STNT1H_MZx_P_BI_4x4 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | 2048 =>
    (do
      (execute_STNT1H_MZx_P_BI_4x4 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | _ => (pure (()))


def decode_STNT1W_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let tstride : Nat := 4
  let t : Int := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize : Nat := 32
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_STNT1W_MZx_P_BI_4x4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_STNT1W_MZx_P_BI_4x4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_STNT1W_MZx_P_BI_4x4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_STNT1W_MZx_P_BI_4x4 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | 2048 =>
    (do
      (execute_STNT1W_MZx_P_BI_4x4 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | _ => (pure (()))


def decode_STNT1D_MZx_P_BI_4x4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (T : (BitVec 1)) (N : (BitVec 1)) (Zt : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  let tstride : Nat := 4
  let t : Int := (BitVec.toNat ((T +++ 0b00#2) +++ Zt))
  let esize : Nat := 64
  let offset : Int := (BitVec.toInt imm4)
  match VL with
  | 128 =>
    (do
      (execute_STNT1D_MZx_P_BI_4x4 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | 256 =>
    (do
      (execute_STNT1D_MZx_P_BI_4x4 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | 512 =>
    (do
      (execute_STNT1D_MZx_P_BI_4x4 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | 1024 =>
    (do
      (execute_STNT1D_MZx_P_BI_4x4 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | 2048 =>
    (do
      (execute_STNT1D_MZx_P_BI_4x4 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) nreg offset (Sail.Int.toNatChecked (t)) tstride))
  | _ => (pure (()))


/-- Type quantifiers: pc : Int -/
def __DecodeA64_SME__seg6 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__433 ← (( do
    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                 __opcode 6 3)) == (0x2#4 : (BitVec 4)))))) : Bool) : Bool)
    then
      (do
        let w__432 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__432 <b 2410) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__433 : Bool)
  then
    (do
      writeReg SEE 2410
      let Zm := (BitVec.slice __opcode 16 4)
      let Rv := (BitVec.slice __opcode 13 2)
      let i2 := (BitVec.slice __opcode 10 2)
      let Zn := (BitVec.slice __opcode 7 3)
      let S := (BitVec.slice __opcode 4 1)
      let off3 := (BitVec.slice __opcode 0 3)
      (decode_FMLS_ZA_ZZi_S4xi Zm Rv i2 Zn S off3)
      (pure false))
  else
    (do
      let w__435 ← (( do
        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     __opcode 12 11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                     __opcode 6 3)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
        then
          (do
            let w__434 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__434 <b 2411) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__435 : Bool)
      then
        (do
          writeReg SEE 2411
          let Zm := (BitVec.slice __opcode 16 4)
          let Rv := (BitVec.slice __opcode 13 2)
          let i1 := (BitVec.slice __opcode 10 1)
          let Zn := (BitVec.slice __opcode 7 3)
          let S := (BitVec.slice __opcode 4 1)
          let off3 := (BitVec.slice __opcode 0 3)
          (decode_FMLA_ZA_ZZi_D4xi Zm Rv i1 Zn S off3)
          (pure false))
      else
        (do
          let w__437 ← (( do
            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         __opcode 12 11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                         __opcode 6 3)) == (0x2#4 : (BitVec 4)))))) : Bool) : Bool)
            then
              (do
                let w__436 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__436 <b 2412) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__437 : Bool)
          then
            (do
              writeReg SEE 2412
              let Zm := (BitVec.slice __opcode 16 4)
              let Rv := (BitVec.slice __opcode 13 2)
              let i1 := (BitVec.slice __opcode 10 1)
              let Zn := (BitVec.slice __opcode 7 3)
              let S := (BitVec.slice __opcode 4 1)
              let off3 := (BitVec.slice __opcode 0 3)
              (decode_FMLS_ZA_ZZi_D4xi Zm Rv i1 Zn S off3)
              (pure false))
          else
            (do
              let w__439 ← (( do
                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                           __opcode 16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 12 10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 5 3)) == (0b010#3 : (BitVec 3)))))) : Bool) : Bool)
                then
                  (do
                    let w__438 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__438 <b 2413) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__439 : Bool)
              then
                (do
                  writeReg SEE 2413
                  let Zm := (BitVec.slice __opcode 17 4)
                  let Rv := (BitVec.slice __opcode 13 2)
                  let Zn := (BitVec.slice __opcode 6 4)
                  let off3 := (BitVec.slice __opcode 0 3)
                  (decode_BFDOT_ZA_ZZW_2x2 Zm Rv Zn off3)
                  (pure false))
              else
                (do
                  let w__441 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 12 10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 __opcode 4 3)) == (0b10#2 : (BitVec 2)))))) : Bool) : Bool)
                    then
                      (do
                        let w__440 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__440 <b 2414) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__441 : Bool)
                  then
                    (do
                      writeReg SEE 2414
                      let Zm := (BitVec.slice __opcode 16 4)
                      let Rv := (BitVec.slice __opcode 13 2)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let off3 := (BitVec.slice __opcode 0 3)
                      (decode_BFDOT_ZA_ZZV_2x1 Zm Rv Zn off3)
                      (pure false))
                  else
                    (do
                      let w__443 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31
                                 21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                     __opcode 12 10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                     __opcode 5 3)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                        then
                          (do
                            let w__442 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__442 <b 2415) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__443 : Bool)
                      then
                        (do
                          writeReg SEE 2415
                          let Zm := (BitVec.slice __opcode 17 4)
                          let Rv := (BitVec.slice __opcode 13 2)
                          let Zn := (BitVec.slice __opcode 6 4)
                          let off3 := (BitVec.slice __opcode 0 3)
                          (decode_FDOT_ZA_ZZW_2x2 Zm Rv Zn off3)
                          (pure false))
                      else
                        (do
                          let w__445 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 12 10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         __opcode 4 3)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                            then
                              (do
                                let w__444 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__444 <b 2416) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__445 : Bool)
                          then
                            (do
                              writeReg SEE 2416
                              let Zm := (BitVec.slice __opcode 16 4)
                              let Rv := (BitVec.slice __opcode 13 2)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let off3 := (BitVec.slice __opcode 0 3)
                              (decode_FDOT_ZA_ZZV_2x1 Zm Rv Zn off3)
                              (pure false))
                          else
                            (do
                              let w__447 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 12 10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                             __opcode 6 3)) == (0x2#4 : (BitVec 4)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__446 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__446 <b 2417) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__447 : Bool)
                              then
                                (do
                                  writeReg SEE 2417
                                  let Zm := (BitVec.slice __opcode 18 3)
                                  let Rv := (BitVec.slice __opcode 13 2)
                                  let Zn := (BitVec.slice __opcode 7 3)
                                  let off3 := (BitVec.slice __opcode 0 3)
                                  (decode_BFDOT_ZA_ZZW_4x4 Zm Rv Zn off3)
                                  (pure false))
                              else
                                (do
                                  let w__449 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 31 20)) == (0xC13#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 12 10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                 __opcode 4 3)) == (0b10#2 : (BitVec 2)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__448 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__448 <b 2418) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__449 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2418
                                      let Zm := (BitVec.slice __opcode 16 4)
                                      let Rv := (BitVec.slice __opcode 13 2)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let off3 := (BitVec.slice __opcode 0 3)
                                      (decode_BFDOT_ZA_ZZV_4x1 Zm Rv Zn off3)
                                      (pure false))
                                  else
                                    (do
                                      let w__451 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                   __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 12 10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                     __opcode 6 3)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__450 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__450 <b 2419) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__451 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2419
                                          let Zm := (BitVec.slice __opcode 18 3)
                                          let Rv := (BitVec.slice __opcode 13 2)
                                          let Zn := (BitVec.slice __opcode 7 3)
                                          let off3 := (BitVec.slice __opcode 0 3)
                                          (decode_FDOT_ZA_ZZW_4x4 Zm Rv Zn off3)
                                          (pure false))
                                      else
                                        (do
                                          let w__453 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 31 20)) == (0xC13#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 12 10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                         __opcode 4 3)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__452 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__452 <b 2420) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__453 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2420
                                              let Zm := (BitVec.slice __opcode 16 4)
                                              let Rv := (BitVec.slice __opcode 13 2)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let off3 := (BitVec.slice __opcode 0 3)
                                              (decode_FDOT_ZA_ZZV_4x1 Zm Rv Zn off3)
                                              (pure false))
                                          else
                                            (do
                                              let w__455 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 5 3)) == (0b011#3 : (BitVec 3)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__454 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__454 <b 2421) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__455 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2421
                                                  let Zm := (BitVec.slice __opcode 16 4)
                                                  let Rv := (BitVec.slice __opcode 13 2)
                                                  let i2 := (BitVec.slice __opcode 10 2)
                                                  let Zn := (BitVec.slice __opcode 6 4)
                                                  let off3 := (BitVec.slice __opcode 0 3)
                                                  (decode_BFDOT_ZA_ZZi_2xi Zm Rv i2 Zn off3)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__457 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                 __opcode 6 3)) == (0x3#4 : (BitVec 4)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__456 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__456 <b 2422) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__457 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2422
                                                      let Zm := (BitVec.slice __opcode 16 4)
                                                      let Rv := (BitVec.slice __opcode 13 2)
                                                      let i2 := (BitVec.slice __opcode 10 2)
                                                      let Zn := (BitVec.slice __opcode 7 3)
                                                      let off3 := (BitVec.slice __opcode 0 3)
                                                      (decode_BFDOT_ZA_ZZi_4xi Zm Rv i2 Zn off3)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__459 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 5 3)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__458 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__458 <b 2423) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__459 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2423
                                                          let Zm := (BitVec.slice __opcode 16 4)
                                                          let Rv := (BitVec.slice __opcode 13 2)
                                                          let i2 := (BitVec.slice __opcode 10 2)
                                                          let Zn := (BitVec.slice __opcode 6 4)
                                                          let off3 := (BitVec.slice __opcode 0 3)
                                                          (decode_FDOT_ZA_ZZi_2xi Zm Rv i2 Zn off3)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__461 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                         __opcode 6 3)) == (0x1#4 : (BitVec 4)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__460 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__460 <b 2424) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__461 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2424
                                                              let Zm := (BitVec.slice __opcode 16 4)
                                                              let Rv := (BitVec.slice __opcode 13 2)
                                                              let i2 := (BitVec.slice __opcode 10 2)
                                                              let Zn := (BitVec.slice __opcode 7 3)
                                                              let off3 :=
                                                                (BitVec.slice __opcode 0 3)
                                                              (decode_FDOT_ZA_ZZi_4xi Zm Rv i2 Zn
                                                                off3)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__463 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                             __opcode 5 3)) == (0b011#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__462 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__462 <b 2425) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__463 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2425
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Rv :=
                                                                    (BitVec.slice __opcode 13 2)
                                                                  let i2 :=
                                                                    (BitVec.slice __opcode 10 2)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 6 4)
                                                                  let off3 :=
                                                                    (BitVec.slice __opcode 0 3)
                                                                  (decode_BFVDOT_ZA_ZZi_2xi Zm Rv i2
                                                                    Zn off3)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__465 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                 __opcode 5 3)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__464 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__464 <b 2426) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__465 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2426
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rv :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let i2 :=
                                                                        (BitVec.slice __opcode 10 2)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 6 4)
                                                                      let off3 :=
                                                                        (BitVec.slice __opcode 0 3)
                                                                      (decode_FVDOT_ZA_ZZi_2xi Zm Rv
                                                                        i2 Zn off3)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__467 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 12 10)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                     __opcode 4 3)) == (0b10#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__466 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__466 <b 2427) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__467 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2427
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
                                                                          (decode_BFMLAL_ZA_ZZV_1 Zm
                                                                            Rv Zn S off3)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__469 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 16
                                                                                       15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                         __opcode 12
                                                                                         10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 5
                                                                                         2)) == (0x4#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__468 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__468 <b 2428) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__469 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2428
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 17 4)
                                                                              let Rv :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 2)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 6 4)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 3 1)
                                                                              let off2 :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 2)
                                                                              (decode_BFMLAL_ZA_ZZW_2x2
                                                                                Zm Rv Zn S off2)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__471 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 2)) == (0b100#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__470 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__470 <b 2429) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__471 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2429
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rv :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 2)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 3 1)
                                                                                  let off2 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 2)
                                                                                  (decode_BFMLAL_ZA_ZZV_2x1
                                                                                    Zm Rv Zn S off2)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__473 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 12
                                                                                                 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 6 2)) == (0b00100#5 : (BitVec 5)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__472 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__472 <b 2430) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__473 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2430
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          18 3)
                                                                                      let Rv :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 2)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 7
                                                                                          3)
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode 3
                                                                                          1)
                                                                                      let off2 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          2)
                                                                                      (decode_BFMLAL_ZA_ZZW_4x4
                                                                                        Zm Rv Zn S
                                                                                        off2)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__475 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0xC13#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     12
                                                                                                     10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     4
                                                                                                     2)) == (0b100#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__474 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__474 <b 2431) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__475 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2431
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
                                                                                          let off2 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 2)
                                                                                          (decode_BFMLAL_ZA_ZZV_4x1
                                                                                            Zm Rv Zn
                                                                                            S off2)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__477 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         12
                                                                                                         10)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         4
                                                                                                         3)) == (0b11#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__476 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__476 <b 2432) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__477 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2432
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
                                                                                              let S :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  3
                                                                                                  1)
                                                                                              let off3 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  3)
                                                                                              (decode_BFMLSL_ZA_ZZV_1
                                                                                                Zm
                                                                                                Rv
                                                                                                Zn S
                                                                                                off3)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__479 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           16
                                                                                                           15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             12
                                                                                                             10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             5
                                                                                                             2)) == (0x6#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__478 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__478 <b 2433) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__479 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2433
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
                                                                                                  let S :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      3
                                                                                                      1)
                                                                                                  let off2 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      2)
                                                                                                  (decode_BFMLSL_ZA_ZZW_2x2
                                                                                                    Zm
                                                                                                    Rv
                                                                                                    Zn
                                                                                                    S
                                                                                                    off2)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__481 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 12
                                                                                                                 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 4
                                                                                                                 2)) == (0b110#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__480 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__480 <b 2434) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__481 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2434
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
                                                                                                      let S :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          3
                                                                                                          1)
                                                                                                      let off2 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          2)
                                                                                                      (decode_BFMLSL_ZA_ZZV_2x1
                                                                                                        Zm
                                                                                                        Rv
                                                                                                        Zn
                                                                                                        S
                                                                                                        off2)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__483 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   17
                                                                                                                   15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     12
                                                                                                                     10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     6
                                                                                                                     2)) == (0b00110#5 : (BitVec 5)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__482 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__482 <b 2435) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__483 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2435
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
                                                                                                          let S :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              3
                                                                                                              1)
                                                                                                          let off2 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              2)
                                                                                                          (decode_BFMLSL_ZA_ZZW_4x4
                                                                                                            Zm
                                                                                                            Rv
                                                                                                            Zn
                                                                                                            S
                                                                                                            off2)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__485 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xC13#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         12
                                                                                                                         10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         4
                                                                                                                         2)) == (0b110#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__484 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__484 <b 2436) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__485 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2436
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
                                                                                                              let S :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  3
                                                                                                                  1)
                                                                                                              let off2 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  2)
                                                                                                              (decode_BFMLSL_ZA_ZZV_4x1
                                                                                                                Zm
                                                                                                                Rv
                                                                                                                Zn
                                                                                                                S
                                                                                                                off2)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__487 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0xC18#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           12
                                                                                                                           12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           4
                                                                                                                           3)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__486 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__486 <b 2437) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__487 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2437
                                                                                                                  let Zm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let i3h :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      15
                                                                                                                      1)
                                                                                                                  let Rv :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      2)
                                                                                                                  let i3l :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      2)
                                                                                                                  let Zn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let S :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      3
                                                                                                                      1)
                                                                                                                  let off3 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      3)
                                                                                                                  (decode_BFMLAL_ZA_ZZi_1
                                                                                                                    Zm
                                                                                                                    i3h
                                                                                                                    Rv
                                                                                                                    i3l
                                                                                                                    Zn
                                                                                                                    S
                                                                                                                    off3)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__489 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xC19#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 12
                                                                                                                                 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 5
                                                                                                                                 3)) == (0b010#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__488 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__488 <b 2438) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__489 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2438
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
                                                                                                                      let i3h :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          2)
                                                                                                                      let Zn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          6
                                                                                                                          4)
                                                                                                                      let S :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          3
                                                                                                                          1)
                                                                                                                      let i3l :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          2
                                                                                                                          1)
                                                                                                                      let off2 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          2)
                                                                                                                      (decode_BFMLAL_ZA_ZZi_2xi
                                                                                                                        Zm
                                                                                                                        Rv
                                                                                                                        i3h
                                                                                                                        Zn
                                                                                                                        S
                                                                                                                        i3l
                                                                                                                        off2)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__491 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 20)) == (0xC19#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     12
                                                                                                                                     12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     6
                                                                                                                                     3)) == (0x2#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__490 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__490 <b 2439) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__491 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2439
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
                                                                                                                          let i3h :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              2)
                                                                                                                          let Zn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              7
                                                                                                                              3)
                                                                                                                          let S :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              3
                                                                                                                              1)
                                                                                                                          let i3l :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              2
                                                                                                                              1)
                                                                                                                          let off2 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              2)
                                                                                                                          (decode_BFMLAL_ZA_ZZi_4xi
                                                                                                                            Zm
                                                                                                                            Rv
                                                                                                                            i3h
                                                                                                                            Zn
                                                                                                                            S
                                                                                                                            i3l
                                                                                                                            off2)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__493 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     20)) == (0xC18#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       12
                                                                                                                                       12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       4
                                                                                                                                       3)) == (0b11#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__492 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__492 <b 2440) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__493 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2440
                                                                                                                              let Zm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let i3h :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  15
                                                                                                                                  1)
                                                                                                                              let Rv :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  13
                                                                                                                                  2)
                                                                                                                              let i3l :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  2)
                                                                                                                              let Zn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let S :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  3
                                                                                                                                  1)
                                                                                                                              let off3 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  3)
                                                                                                                              (decode_BFMLSL_ZA_ZZi_1
                                                                                                                                Zm
                                                                                                                                i3h
                                                                                                                                Rv
                                                                                                                                i3l
                                                                                                                                Zn
                                                                                                                                S
                                                                                                                                off3)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__495 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         20)) == (0xC19#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             12
                                                                                                                                             12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             5
                                                                                                                                             3)) == (0b011#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__494 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__494 <b 2441) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__495 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2441
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
                                                                                                                                  let i3h :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      2)
                                                                                                                                  let Zn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      6
                                                                                                                                      4)
                                                                                                                                  let S :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      3
                                                                                                                                      1)
                                                                                                                                  let i3l :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      2
                                                                                                                                      1)
                                                                                                                                  let off2 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      2)
                                                                                                                                  (decode_BFMLSL_ZA_ZZi_2xi
                                                                                                                                    Zm
                                                                                                                                    Rv
                                                                                                                                    i3h
                                                                                                                                    Zn
                                                                                                                                    S
                                                                                                                                    i3l
                                                                                                                                    off2)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__497 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             20)) == (0xC19#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 12
                                                                                                                                                 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 6
                                                                                                                                                 3)) == (0x3#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__496 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__496 <b 2442) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__497 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2442
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
                                                                                                                                      let i3h :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          2)
                                                                                                                                      let Zn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          7
                                                                                                                                          3)
                                                                                                                                      let S :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          3
                                                                                                                                          1)
                                                                                                                                      let i3l :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          2
                                                                                                                                          1)
                                                                                                                                      let off2 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          2)
                                                                                                                                      (decode_BFMLSL_ZA_ZZi_4xi
                                                                                                                                        Zm
                                                                                                                                        Rv
                                                                                                                                        i3h
                                                                                                                                        Zn
                                                                                                                                        S
                                                                                                                                        i3l
                                                                                                                                        off2)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__499 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     12
                                                                                                                                                     10)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     4
                                                                                                                                                     3)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__498 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__498 <b 2443) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__499 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2443
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
                                                                                                                                          let S :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              3
                                                                                                                                              1)
                                                                                                                                          let off3 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              3)
                                                                                                                                          (decode_FMLAL_ZA_ZZV_1
                                                                                                                                            Zm
                                                                                                                                            Rv
                                                                                                                                            Zn
                                                                                                                                            S
                                                                                                                                            off3)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__501 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       16
                                                                                                                                                       15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         12
                                                                                                                                                         10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         5
                                                                                                                                                         2)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__500 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__500 <b 2444) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__501 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2444
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
                                                                                                                                              let S :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  3
                                                                                                                                                  1)
                                                                                                                                              let off2 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  2)
                                                                                                                                              (decode_FMLAL_ZA_ZZW_2x2
                                                                                                                                                Zm
                                                                                                                                                Rv
                                                                                                                                                Zn
                                                                                                                                                S
                                                                                                                                                off2)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__503 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           15
                                                                                                                                                           15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             12
                                                                                                                                                             10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             4
                                                                                                                                                             2)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__502 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__502 <b 2445) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__503 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2445
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
                                                                                                                                                  let S :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      3
                                                                                                                                                      1)
                                                                                                                                                  let off2 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      2)
                                                                                                                                                  (decode_FMLAL_ZA_ZZV_2x1
                                                                                                                                                    Zm
                                                                                                                                                    Rv
                                                                                                                                                    Zn
                                                                                                                                                    S
                                                                                                                                                    off2)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
