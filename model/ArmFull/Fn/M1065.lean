import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0977
import ArmFull.Fn.M0978
import ArmFull.Fn.M0979
import ArmFull.Fn.M0980
import ArmFull.Fn.M1026

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

/-- Type quantifiers: pc : Int -/
def __DecodeA64_SVE__seg18 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1467 ← (( do
    if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb __opcode 31 10)) == (0b0100010100100011111000#22 : (BitVec 22))) : Bool) : Bool)
    then
      (do
        let w__1466 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1466 <b 1770) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1467 : Bool)
  then
    (do
      writeReg SEE 1770
      let size := (BitVec.slice __opcode 22 2)
      let Zm := (BitVec.slice __opcode 5 5)
      let Zdn := (BitVec.slice __opcode 0 5)
      (decode_SM4E_Z_ZZ__ size Zm Zdn)
      (pure false))
  else
    (do
      let w__1469 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b01000101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                 __opcode 15 10)) == (0b111100#6 : (BitVec 6)))) : Bool) : Bool)
        then
          (do
            let w__1468 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1468 <b 1771) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1469 : Bool)
      then
        (do
          writeReg SEE 1771
          let size := (BitVec.slice __opcode 22 2)
          let Zm := (BitVec.slice __opcode 16 5)
          let Zn := (BitVec.slice __opcode 5 5)
          let Zd := (BitVec.slice __opcode 0 5)
          (decode_SM4EKEY_Z_ZZ__ size Zm Zn Zd)
          (pure false))
      else
        (do
          let w__1471 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                       __opcode 15 10)) == (0b001101#6 : (BitVec 6))))) : Bool) : Bool)
            then
              (do
                let w__1470 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1470 <b 1772) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1471 : Bool)
          then
            (do
              writeReg SEE 1772
              let tszh := (BitVec.slice __opcode 22 2)
              let tszl := (BitVec.slice __opcode 19 2)
              let imm3 := (BitVec.slice __opcode 16 3)
              let Zm := (BitVec.slice __opcode 5 5)
              let Zdn := (BitVec.slice __opcode 0 5)
              (decode_XAR_Z_ZZI__ tszh tszl imm3 Zm Zdn)
              (pure false))
          else
            (do
              let w__1473 ← (( do
                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00000100011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                         __opcode 15 10)) == (0b001110#6 : (BitVec 6)))) : Bool) : Bool)
                then
                  (do
                    let w__1472 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1472 <b 1773) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1473 : Bool)
              then
                (do
                  writeReg SEE 1773
                  let Zm := (BitVec.slice __opcode 16 5)
                  let Zk := (BitVec.slice __opcode 5 5)
                  let Zdn := (BitVec.slice __opcode 0 5)
                  (decode_BCAX_Z_ZZZ__ Zm Zk Zdn)
                  (pure false))
              else
                (do
                  let w__1475 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00000100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                             __opcode 15 10)) == (0b001110#6 : (BitVec 6)))) : Bool) : Bool)
                    then
                      (do
                        let w__1474 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1474 <b 1774) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1475 : Bool)
                  then
                    (do
                      writeReg SEE 1774
                      let Zm := (BitVec.slice __opcode 16 5)
                      let Zk := (BitVec.slice __opcode 5 5)
                      let Zdn := (BitVec.slice __opcode 0 5)
                      (decode_EOR3_Z_ZZZ__ Zm Zk Zdn)
                      (pure false))
                  else
                    (do
                      let w__1477 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31
                                 21)) == (0b00000100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                 __opcode 15 10)) == (0b001111#6 : (BitVec 6)))) : Bool) : Bool)
                        then
                          (do
                            let w__1476 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1476 <b 1775) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1477 : Bool)
                      then
                        (do
                          writeReg SEE 1775
                          let Zm := (BitVec.slice __opcode 16 5)
                          let Zk := (BitVec.slice __opcode 5 5)
                          let Zdn := (BitVec.slice __opcode 0 5)
                          (decode_BSL_Z_ZZZ__ Zm Zk Zdn)
                          (pure false))
                      else
                        (do
                          let w__1479 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode
                                     31 21)) == (0b00000100011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                     __opcode 15 10)) == (0b001111#6 : (BitVec 6)))) : Bool) : Bool)
                            then
                              (do
                                let w__1478 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1478 <b 1776) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1479 : Bool)
                          then
                            (do
                              writeReg SEE 1776
                              let Zm := (BitVec.slice __opcode 16 5)
                              let Zk := (BitVec.slice __opcode 5 5)
                              let Zdn := (BitVec.slice __opcode 0 5)
                              (decode_BSL1N_Z_ZZZ__ Zm Zk Zdn)
                              (pure false))
                          else
                            (do
                              let w__1481 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b00000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                         __opcode 15 10)) == (0b001111#6 : (BitVec 6)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1480 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1480 <b 1777) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1481 : Bool)
                              then
                                (do
                                  writeReg SEE 1777
                                  let Zm := (BitVec.slice __opcode 16 5)
                                  let Zk := (BitVec.slice __opcode 5 5)
                                  let Zdn := (BitVec.slice __opcode 0 5)
                                  (decode_BSL2N_Z_ZZZ__ Zm Zk Zdn)
                                  (pure false))
                              else
                                (do
                                  let w__1483 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 31 21)) == (0b00000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                             __opcode 15 10)) == (0b001111#6 : (BitVec 6)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1482 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1482 <b 1778) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1483 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1778
                                      let Zm := (BitVec.slice __opcode 16 5)
                                      let Zk := (BitVec.slice __opcode 5 5)
                                      let Zdn := (BitVec.slice __opcode 0 5)
                                      (decode_NBSL_Z_ZZZ__ Zm Zk Zdn)
                                      (pure false))
                                  else
                                    (do
                                      let w__1485 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 15 10)) == (0b110100#6 : (BitVec 6))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1484 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1484 <b 1779) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1485 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1779
                                          let sz := (BitVec.slice __opcode 22 1)
                                          let Zm := (BitVec.slice __opcode 16 5)
                                          let T := (BitVec.slice __opcode 10 1)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let Zda := (BitVec.slice __opcode 0 5)
                                          (decode_ADCLB_Z_ZZZ__ sz Zm T Zn Zda)
                                          (pure false))
                                      else
                                        (do
                                          let w__1487 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b010001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 15 10)) == (0b110101#6 : (BitVec 6))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1486 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1486 <b 1780) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1487 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1780
                                              let sz := (BitVec.slice __opcode 22 1)
                                              let Zm := (BitVec.slice __opcode 16 5)
                                              let T := (BitVec.slice __opcode 10 1)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zda := (BitVec.slice __opcode 0 5)
                                              (decode_ADCLT_Z_ZZZ__ sz Zm T Zn Zda)
                                              (pure false))
                                          else
                                            (do
                                              let w__1489 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b010001011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 15 10)) == (0b110100#6 : (BitVec 6))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1488 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1488 <b 1781) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1489 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1781
                                                  let sz := (BitVec.slice __opcode 22 1)
                                                  let Zm := (BitVec.slice __opcode 16 5)
                                                  let T := (BitVec.slice __opcode 10 1)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let Zda := (BitVec.slice __opcode 0 5)
                                                  (decode_SBCLB_Z_ZZZ__ sz Zm T Zn Zda)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1491 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b010001011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 15 10)) == (0b110101#6 : (BitVec 6))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1490 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1490 <b 1782) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1491 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1782
                                                      let sz := (BitVec.slice __opcode 22 1)
                                                      let Zm := (BitVec.slice __opcode 16 5)
                                                      let T := (BitVec.slice __opcode 10 1)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let Zda := (BitVec.slice __opcode 0 5)
                                                      (decode_SBCLT_Z_ZZZ__ sz Zm T Zn Zda)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1493 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 15 10)) == (0b011010#6 : (BitVec 6))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1492 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1492 <b 1783) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1493 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1783
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let Zm := (BitVec.slice __opcode 16 5)
                                                          let U := (BitVec.slice __opcode 10 1)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let Zd := (BitVec.slice __opcode 0 5)
                                                          (decode_SMULH_Z_ZZ__ size Zm U Zn Zd)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1495 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 15 10)) == (0b011011#6 : (BitVec 6))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1494 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1494 <b 1784) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1495 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1784
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let Zm := (BitVec.slice __opcode 16 5)
                                                              let U := (BitVec.slice __opcode 10 1)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let Zd := (BitVec.slice __opcode 0 5)
                                                              (decode_UMULH_Z_ZZ__ size Zm U Zn Zd)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1497 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 15 10)) == (0b110000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1496 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1496 <b 1785) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1497 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1785
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 10 1)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_SCLAMP_Z_ZZ__ size Zm U Zn
                                                                    Zd)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1499 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 15 10)) == (0b110001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1498 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1498 <b 1786) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1499 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1786
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 10 1)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_UCLAMP_Z_ZZ__ size Zm
                                                                        U Zn Zd)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1501 ← (( do
                                                                        if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                               __opcode 31 13)) == (0b0000010100101110100#19 : (BitVec 19))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1500 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1500 <b 1787) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1501 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1787
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let Pg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_REVD_Z_P_Z__ size
                                                                            Pg Zn Zd)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1503 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         14)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           9 9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1502 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1502 <b 1788) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1503 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1788
                                                                              let i1 :=
                                                                                (BitVec.slice
                                                                                  __opcode 23 1)
                                                                              let tszh :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let tszl :=
                                                                                (BitVec.slice
                                                                                  __opcode 18 3)
                                                                              let Rv :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 2)
                                                                              let Pn :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 4)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 9 1)
                                                                              let Pm :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 4)
                                                                              let Pd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_PSEL_P_PPi__
                                                                                i1 tszh tszl Rv Pn S
                                                                                Pm Pd)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1505 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 10)) == (0b010111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               4 4)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               0 0)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1504 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1504 <b 1789) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1505 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1789
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 11 1)
                                                                                  let lt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 1)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Pd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 1 3)
                                                                                  let eq :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 1)
                                                                                  (decode_WHILELO_PP_RR__
                                                                                    size Rm U lt Rn
                                                                                    Pd eq)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1507 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 10)) == (0b010111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   4
                                                                                                   4)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   0
                                                                                                   0)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1506 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1506 <b 1790) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1507 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1790
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          11 1)
                                                                                      let lt :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 1)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Pd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 1
                                                                                          3)
                                                                                      let eq :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          1)
                                                                                      (decode_WHILELS_PP_RR__
                                                                                        size Rm U lt
                                                                                        Rn Pd eq)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1509 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     10)) == (0b010101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       4
                                                                                                       4)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       0
                                                                                                       0)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1508 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1508 <b 1791) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1509 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1791
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              11 1)
                                                                                          let lt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 1)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Pd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              1 3)
                                                                                          let eq :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 1)
                                                                                          (decode_WHILELT_PP_RR__
                                                                                            size Rm
                                                                                            U lt Rn
                                                                                            Pd eq)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1511 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         10)) == (0b010101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           4
                                                                                                           4)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           0
                                                                                                           0)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1510 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1510 <b 1792) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1511 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1792
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  5)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  11
                                                                                                  1)
                                                                                              let lt :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  1)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let Pd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  1
                                                                                                  3)
                                                                                              let eq :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  1)
                                                                                              (decode_WHILELE_PP_RR__
                                                                                                size
                                                                                                Rm U
                                                                                                lt
                                                                                                Rn
                                                                                                Pd
                                                                                                eq)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1513 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             10)) == (0b010110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               4
                                                                                                               4)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               0
                                                                                                               0)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1512 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1512 <b 1793) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1513 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1793
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      2)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      11
                                                                                                      1)
                                                                                                  let lt :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      1)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let Pd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      1
                                                                                                      3)
                                                                                                  let eq :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      1)
                                                                                                  (decode_WHILEHI_PP_RR__
                                                                                                    size
                                                                                                    Rm
                                                                                                    U
                                                                                                    lt
                                                                                                    Rn
                                                                                                    Pd
                                                                                                    eq)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1515 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 10)) == (0b010110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   4
                                                                                                                   4)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   0
                                                                                                                   0)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1514 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1514 <b 1794) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1515 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1794
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          2)
                                                                                                      let Rm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          5)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          11
                                                                                                          1)
                                                                                                      let lt :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          1)
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let Pd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          1
                                                                                                          3)
                                                                                                      let eq :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          1)
                                                                                                      (decode_WHILEHS_PP_RR__
                                                                                                        size
                                                                                                        Rm
                                                                                                        U
                                                                                                        lt
                                                                                                        Rn
                                                                                                        Pd
                                                                                                        eq)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1517 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     10)) == (0b010100#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       4
                                                                                                                       4)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       0
                                                                                                                       0)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1516 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1516 <b 1795) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1517 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1795
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              2)
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              11
                                                                                                              1)
                                                                                                          let lt :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              1)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let Pd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              1
                                                                                                              3)
                                                                                                          let eq :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              1)
                                                                                                          (decode_WHILEGT_PP_RR__
                                                                                                            size
                                                                                                            Rm
                                                                                                            U
                                                                                                            lt
                                                                                                            Rn
                                                                                                            Pd
                                                                                                            eq)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1519 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         10)) == (0b010100#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           4
                                                                                                                           4)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           0
                                                                                                                           0)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1518 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1518 <b 1796) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1519 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1796
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
                                                                                                              let Rm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  11
                                                                                                                  1)
                                                                                                              let lt :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  1)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let Pd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  1
                                                                                                                  3)
                                                                                                              let eq :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  1)
                                                                                                              (decode_WHILEGE_PP_RR__
                                                                                                                size
                                                                                                                Rm
                                                                                                                U
                                                                                                                lt
                                                                                                                Rn
                                                                                                                Pd
                                                                                                                eq)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1521 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0x45B#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           10)) == (0b001010#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           5
                                                                                                                           5)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1520 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1520 <b 1797) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1521 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1797
                                                                                                                  let tszh :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let tszl :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      20
                                                                                                                      1)
                                                                                                                  let imm4 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      1)
                                                                                                                  let R :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      11
                                                                                                                      1)
                                                                                                                  let Zn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      6
                                                                                                                      4)
                                                                                                                  let Zd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  (decode_SQRSHRN_Z_MZ2__
                                                                                                                    tszh
                                                                                                                    tszl
                                                                                                                    imm4
                                                                                                                    U
                                                                                                                    R
                                                                                                                    Zn
                                                                                                                    Zd)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1523 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0x45B#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               10)) == (0b000010#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               5
                                                                                                                               5)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1522 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1522 <b 1798) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1523 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1798
                                                                                                                      let tszh :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          1)
                                                                                                                      let tszl :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          20
                                                                                                                          1)
                                                                                                                      let imm4 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          1)
                                                                                                                      let R :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          11
                                                                                                                          1)
                                                                                                                      let Zn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          6
                                                                                                                          4)
                                                                                                                      let Zd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      (decode_SQRSHRUN_Z_MZ2__
                                                                                                                        tszh
                                                                                                                        tszl
                                                                                                                        imm4
                                                                                                                        U
                                                                                                                        R
                                                                                                                        Zn
                                                                                                                        Zd)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1525 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 20)) == (0x45B#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   10)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   5
                                                                                                                                   5)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1524 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1524 <b 1799) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1525 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1799
                                                                                                                          let tszh :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let tszl :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              20
                                                                                                                              1)
                                                                                                                          let imm4 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              1)
                                                                                                                          let R :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              11
                                                                                                                              1)
                                                                                                                          let Zn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              6
                                                                                                                              4)
                                                                                                                          let Zd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          (decode_UQRSHRN_Z_MZ2__
                                                                                                                            tszh
                                                                                                                            tszl
                                                                                                                            imm4
                                                                                                                            U
                                                                                                                            R
                                                                                                                            Zn
                                                                                                                            Zd)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1527 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     10)) == (0b0100010100110001010000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     5
                                                                                                                                     5)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1526 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1526 <b 1800) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1527 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1800
                                                                                                                              let tszh :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  1)
                                                                                                                              let tszl :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  19
                                                                                                                                  2)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  11
                                                                                                                                  1)
                                                                                                                              let Zn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  6
                                                                                                                                  4)
                                                                                                                              let Zd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              (decode_SQCVTN_Z_MZ2__
                                                                                                                                tszh
                                                                                                                                tszl
                                                                                                                                U
                                                                                                                                Zn
                                                                                                                                Zd)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1529 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         10)) == (0b0100010100110001010100#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         5
                                                                                                                                         5)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1528 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1528 <b 1801) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1529 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1801
                                                                                                                                  let tszh :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      1)
                                                                                                                                  let tszl :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      19
                                                                                                                                      2)
                                                                                                                                  let Zn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      6
                                                                                                                                      4)
                                                                                                                                  let Zd :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  (decode_SQCVTUN_Z_MZ2__
                                                                                                                                    tszh
                                                                                                                                    tszl
                                                                                                                                    Zn
                                                                                                                                    Zd)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1531 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             10)) == (0b0100010100110001010010#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             5
                                                                                                                                             5)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1530 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1530 <b 1802) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1531 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1802
                                                                                                                                      let tszh :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          1)
                                                                                                                                      let tszl :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          19
                                                                                                                                          2)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          11
                                                                                                                                          1)
                                                                                                                                      let Zn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          6
                                                                                                                                          4)
                                                                                                                                      let Zd :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      (decode_UQCVTN_Z_MZ2__
                                                                                                                                        tszh
                                                                                                                                        tszl
                                                                                                                                        U
                                                                                                                                        Zn
                                                                                                                                        Zd)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1533 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b00000101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 10)) == (0b001001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1532 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1532 <b 1803) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1533 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1803
                                                                                                                                          let i1 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              20
                                                                                                                                              1)
                                                                                                                                          let tsz :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let Zn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let Zd :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_DUPQ_Z_Zi__
                                                                                                                                            i1
                                                                                                                                            tsz
                                                                                                                                            Zn
                                                                                                                                            Zd)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1535 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     20)) == (0x056#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     10)) == (0b001001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1534 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1534 <b 1804) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1535 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1804
                                                                                                                                              let imm4 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  4)
                                                                                                                                              let Zm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let Zdn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              (decode_EXTQ_Z_ZI_Des
                                                                                                                                                imm4
                                                                                                                                                Zm
                                                                                                                                                Zdn)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__1537 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           21
                                                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           15
                                                                                                                                                           10)) == (0b111110#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__1536 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__1536 <b 1805) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__1537 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1805
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
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_TBLQ_Z_ZZ__
                                                                                                                                                    size
                                                                                                                                                    Zm
                                                                                                                                                    Zn
                                                                                                                                                    Zd)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__1539 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               21
                                                                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               15
                                                                                                                                                               10)) == (0b001101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__1538 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__1538 <b 1806) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__1539 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1806
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
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_TBXQ_Z_ZZ__
                                                                                                                                                        size
                                                                                                                                                        Zm
                                                                                                                                                        Zn
                                                                                                                                                        Zd)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__1541 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   21
                                                                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   15
                                                                                                                                                                   10)) == (0b111010#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__1540 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__1540 <b 1807) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__1541 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1807
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
                                                                                                                                                          let H :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              1)
                                                                                                                                                          let Zn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              5)
                                                                                                                                                          let Zd :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          (decode_UZPQ1_Z_ZZ__
                                                                                                                                                            size
                                                                                                                                                            Zm
                                                                                                                                                            H
                                                                                                                                                            Zn
                                                                                                                                                            Zd)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__1543 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       21
                                                                                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       15
                                                                                                                                                                       10)) == (0b111011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__1542 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__1542 <b 1808) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__1543 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 1808
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
                                                                                                                                                              let H :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  10
                                                                                                                                                                  1)
                                                                                                                                                              let Zn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  5)
                                                                                                                                                              let Zd :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  5)
                                                                                                                                                              (decode_UZPQ2_Z_ZZ__
                                                                                                                                                                size
                                                                                                                                                                Zm
                                                                                                                                                                H
                                                                                                                                                                Zn
                                                                                                                                                                Zd)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__1545 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           21
                                                                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           15
                                                                                                                                                                           10)) == (0b111000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__1544 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__1544 <b 1809) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__1545 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 1809
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
                                                                                                                                                                  let H :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      10
                                                                                                                                                                      1)
                                                                                                                                                                  let Zn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      5
                                                                                                                                                                      5)
                                                                                                                                                                  let Zd :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      5)
                                                                                                                                                                  (decode_ZIPQ1_Z_ZZ__
                                                                                                                                                                    size
                                                                                                                                                                    Zm
                                                                                                                                                                    H
                                                                                                                                                                    Zn
                                                                                                                                                                    Zd)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
