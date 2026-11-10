import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0974
import ArmFull.Fn.M0975
import ArmFull.Fn.M0976
import ArmFull.Fn.M0977
import ArmFull.Fn.M1025
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
def __DecodeA64_SVE__seg17 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1383 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
             __opcode 21 13)) == (0b011000100#9 : (BitVec 9)))) : Bool) : Bool)
    then
      (do
        let w__1382 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1382 <b 1728) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1383 : Bool)
  then
    (do
      writeReg SEE 1728
      let size := (BitVec.slice __opcode 22 2)
      let S := (BitVec.slice __opcode 17 1)
      let U := (BitVec.slice __opcode 16 1)
      let Pg := (BitVec.slice __opcode 10 3)
      let Zm := (BitVec.slice __opcode 5 5)
      let Zdn := (BitVec.slice __opcode 0 5)
      (decode_SQADD_Z_P_ZZ__ size S U Pg Zm Zdn)
      (pure false))
  else
    (do
      let w__1385 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                 __opcode 21 13)) == (0b011001100#9 : (BitVec 9)))) : Bool) : Bool)
        then
          (do
            let w__1384 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1384 <b 1729) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1385 : Bool)
      then
        (do
          writeReg SEE 1729
          let size := (BitVec.slice __opcode 22 2)
          let S := (BitVec.slice __opcode 17 1)
          let U := (BitVec.slice __opcode 16 1)
          let Pg := (BitVec.slice __opcode 10 3)
          let Zm := (BitVec.slice __opcode 5 5)
          let Zdn := (BitVec.slice __opcode 0 5)
          (decode_UQADD_Z_P_ZZ__ size S U Pg Zm Zdn)
          (pure false))
      else
        (do
          let w__1387 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                     __opcode 21 13)) == (0b011010100#9 : (BitVec 9)))) : Bool) : Bool)
            then
              (do
                let w__1386 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1386 <b 1730) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1387 : Bool)
          then
            (do
              writeReg SEE 1730
              let size := (BitVec.slice __opcode 22 2)
              let S := (BitVec.slice __opcode 17 1)
              let U := (BitVec.slice __opcode 16 1)
              let Pg := (BitVec.slice __opcode 10 3)
              let Zm := (BitVec.slice __opcode 5 5)
              let Zdn := (BitVec.slice __opcode 0 5)
              (decode_SQSUB_Z_P_ZZ__ size S U Pg Zm Zdn)
              (pure false))
          else
            (do
              let w__1389 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                         __opcode 21 13)) == (0b011011100#9 : (BitVec 9)))) : Bool) : Bool)
                then
                  (do
                    let w__1388 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1388 <b 1731) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1389 : Bool)
              then
                (do
                  writeReg SEE 1731
                  let size := (BitVec.slice __opcode 22 2)
                  let S := (BitVec.slice __opcode 17 1)
                  let U := (BitVec.slice __opcode 16 1)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let Zm := (BitVec.slice __opcode 5 5)
                  let Zdn := (BitVec.slice __opcode 0 5)
                  (decode_UQSUB_Z_P_ZZ__ size S U Pg Zm Zdn)
                  (pure false))
              else
                (do
                  let w__1391 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                             __opcode 21 13)) == (0b011110100#9 : (BitVec 9)))) : Bool) : Bool)
                    then
                      (do
                        let w__1390 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1390 <b 1732) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1391 : Bool)
                  then
                    (do
                      writeReg SEE 1732
                      let size := (BitVec.slice __opcode 22 2)
                      let S := (BitVec.slice __opcode 17 1)
                      let U := (BitVec.slice __opcode 16 1)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Zm := (BitVec.slice __opcode 5 5)
                      let Zdn := (BitVec.slice __opcode 0 5)
                      (decode_SQSUBR_Z_P_ZZ__ size S U Pg Zm Zdn)
                      (pure false))
                  else
                    (do
                      let w__1393 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                 __opcode 21 13)) == (0b011111100#9 : (BitVec 9)))) : Bool) : Bool)
                        then
                          (do
                            let w__1392 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1392 <b 1733) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1393 : Bool)
                      then
                        (do
                          writeReg SEE 1733
                          let size := (BitVec.slice __opcode 22 2)
                          let S := (BitVec.slice __opcode 17 1)
                          let U := (BitVec.slice __opcode 16 1)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Zm := (BitVec.slice __opcode 5 5)
                          let Zdn := (BitVec.slice __opcode 0 5)
                          (decode_UQSUBR_Z_P_ZZ__ size S U Pg Zm Zdn)
                          (pure false))
                      else
                        (do
                          let w__1395 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                     __opcode 21 13)) == (0b011100100#9 : (BitVec 9)))) : Bool) : Bool)
                            then
                              (do
                                let w__1394 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1394 <b 1734) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1395 : Bool)
                          then
                            (do
                              writeReg SEE 1734
                              let size := (BitVec.slice __opcode 22 2)
                              let S := (BitVec.slice __opcode 17 1)
                              let U := (BitVec.slice __opcode 16 1)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Zm := (BitVec.slice __opcode 5 5)
                              let Zdn := (BitVec.slice __opcode 0 5)
                              (decode_SUQADD_Z_P_ZZ__ size S U Pg Zm Zdn)
                              (pure false))
                          else
                            (do
                              let w__1397 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 21 13)) == (0b011101100#9 : (BitVec 9)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1396 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1396 <b 1735) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1397 : Bool)
                              then
                                (do
                                  writeReg SEE 1735
                                  let size := (BitVec.slice __opcode 22 2)
                                  let S := (BitVec.slice __opcode 17 1)
                                  let U := (BitVec.slice __opcode 16 1)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Zm := (BitVec.slice __opcode 5 5)
                                  let Zdn := (BitVec.slice __opcode 0 5)
                                  (decode_USQADD_Z_P_ZZ__ size S U Pg Zm Zdn)
                                  (pure false))
                              else
                                (do
                                  let w__1399 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                               __opcode 15 10)) == (0b111101#6 : (BitVec 6))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1398 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1398 <b 1736) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1399 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1736
                                      let tszh := (BitVec.slice __opcode 22 2)
                                      let tszl := (BitVec.slice __opcode 19 2)
                                      let imm3 := (BitVec.slice __opcode 16 3)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let Zd := (BitVec.slice __opcode 0 5)
                                      (decode_SLI_Z_ZZI__ tszh tszl imm3 Zn Zd)
                                      (pure false))
                                  else
                                    (do
                                      let w__1401 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 15 10)) == (0b111100#6 : (BitVec 6))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1400 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1400 <b 1737) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1401 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1737
                                          let tszh := (BitVec.slice __opcode 22 2)
                                          let tszl := (BitVec.slice __opcode 19 2)
                                          let imm3 := (BitVec.slice __opcode 16 3)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let Zd := (BitVec.slice __opcode 0 5)
                                          (decode_SRI_Z_ZZI__ tszh tszl imm3 Zn Zd)
                                          (pure false))
                                      else
                                        (do
                                          let w__1403 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 15 10)) == (0b001011#6 : (BitVec 6))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1402 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1402 <b 1738) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1403 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1738
                                              let size := (BitVec.slice __opcode 22 2)
                                              let Zm := (BitVec.slice __opcode 16 5)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zd := (BitVec.slice __opcode 0 5)
                                              (decode_TBX_Z_ZZ__ size Zm Zn Zd)
                                              (pure false))
                                          else
                                            (do
                                              let w__1405 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 21 13)) == (0b000000101#9 : (BitVec 9)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1404 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1404 <b 1739) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1405 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1739
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let Q := (BitVec.slice __opcode 19 1)
                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let Zd := (BitVec.slice __opcode 0 5)
                                                  (decode_URECPE_Z_P_Z__ size Q Pg Zn Zd)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1407 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 21 13)) == (0b000001101#9 : (BitVec 9)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1406 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1406 <b 1740) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1407 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1740
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let Q := (BitVec.slice __opcode 19 1)
                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let Zd := (BitVec.slice __opcode 0 5)
                                                      (decode_URSQRTE_Z_P_Z__ size Q Pg Zn Zd)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1409 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 15 13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1408 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1408 <b 1741) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1409 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1741
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let Zm := (BitVec.slice __opcode 16 5)
                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let Pd := (BitVec.slice __opcode 0 4)
                                                          (decode_MATCH_P_P_ZZ__ size Zm Pg Zn Pd)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1411 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                         __opcode 15 13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1410 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1410 <b 1742) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1411 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1742
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let Zm := (BitVec.slice __opcode 16 5)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let Pd := (BitVec.slice __opcode 0 4)
                                                              (decode_NMATCH_P_P_ZZ__ size Zm Pg Zn
                                                                Pd)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1413 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 15 13)) == (0b110#3 : (BitVec 3))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1412 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1412 <b 1743) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1413 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1743
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_HISTCNT_Z_P_ZZ__ size Zm
                                                                    Pg Zn Zd)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1415 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 15 10)) == (0b101000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1414 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1414 <b 1744) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1415 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1744
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_HISTSEG_Z_ZZ__ size Zm
                                                                        Zn Zd)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1417 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 10)) == (0b001100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1416 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1416 <b 1745) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1417 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1745
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let rw :=
                                                                            (BitVec.slice __opcode 4
                                                                              1)
                                                                          let Pd :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_WHILEWR_P_RR__
                                                                            size Rm Rn rw Pd)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1419 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         10)) == (0b001100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 4
                                                                                         4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1418 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1418 <b 1746) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1419 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1746
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let rw :=
                                                                                (BitVec.slice
                                                                                  __opcode 4 1)
                                                                              let Pd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_WHILERW_P_RR__
                                                                                size Rm Rn rw Pd)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1421 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 10)) == (0b101101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1420 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1420 <b 1747) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1421 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1747
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Zd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_BDEP_Z_ZZ__
                                                                                    size Zm Zn Zd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1423 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 10)) == (0b101100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1422 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1422 <b 1748) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1423 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1748
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Zd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_BEXT_Z_ZZ__
                                                                                        size Zm Zn
                                                                                        Zd)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1425 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   10)) == (0b101110#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1424 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1424 <b 1749) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1425 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1749
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Zd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_BGRP_Z_ZZ__
                                                                                            size Zm
                                                                                            Zn Zd)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1427 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       10)) == (0b100100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1426 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1426 <b 1750) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1427 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1750
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
                                                                                              let tb :=
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
                                                                                              (decode_EORBT_Z_ZZ__
                                                                                                size
                                                                                                Zm
                                                                                                tb
                                                                                                Zn
                                                                                                Zd)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1429 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           10)) == (0b100101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1428 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1428 <b 1751) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1429 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1751
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
                                                                                                  let tb :=
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
                                                                                                  (decode_EORTB_Z_ZZ__
                                                                                                    size
                                                                                                    Zm
                                                                                                    tb
                                                                                                    Zn
                                                                                                    Zd)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1431 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               12)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1430 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1430 <b 1752) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1431 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1752
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
                                                                                                      let rot :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          2)
                                                                                                      let Zn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let Zda :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      (decode_CDOT_Z_ZZZ__
                                                                                                        size
                                                                                                        Zm
                                                                                                        rot
                                                                                                        Zn
                                                                                                        Zda)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1433 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 12)) == (0x4#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1432 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1432 <b 1753) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1433 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1753
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              2)
                                                                                                          let i2 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              19
                                                                                                              2)
                                                                                                          let Zm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              3)
                                                                                                          let rot :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              2)
                                                                                                          let Zn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let Zda :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          (decode_CDOT_Z_ZZZi_S
                                                                                                            size
                                                                                                            i2
                                                                                                            Zm
                                                                                                            rot
                                                                                                            Zn
                                                                                                            Zda)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1435 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     21)) == (0b01000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     12)) == (0x4#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1434 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1434 <b 1754) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1435 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1754
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
                                                                                                              let i1 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  20
                                                                                                                  1)
                                                                                                              let Zm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let rot :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  2)
                                                                                                              let Zn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let Zda :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              (decode_CDOT_Z_ZZZi_D
                                                                                                                size
                                                                                                                i1
                                                                                                                Zm
                                                                                                                rot
                                                                                                                Zn
                                                                                                                Zda)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1437 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         21)) == (0b01000101000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         10)) == (0b100110#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1436 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1436 <b 1755) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1437 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1755
                                                                                                                  let uns :=
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
                                                                                                                  let Zda :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  (decode_SMMLA_Z_ZZZ__
                                                                                                                    uns
                                                                                                                    Zm
                                                                                                                    Zn
                                                                                                                    Zda)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1439 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             21)) == (0b01000101110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             10)) == (0b100110#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1438 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1438 <b 1756) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1439 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1756
                                                                                                                      let uns :=
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
                                                                                                                      let Zda :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      (decode_UMMLA_Z_ZZZ__
                                                                                                                        uns
                                                                                                                        Zm
                                                                                                                        Zn
                                                                                                                        Zda)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1441 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b01000101100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 15
                                                                                                                                 10)) == (0b100110#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1440 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1440 <b 1757) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1441 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1757
                                                                                                                          let uns :=
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
                                                                                                                          let Zda :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          (decode_USMMLA_Z_ZZZ__
                                                                                                                            uns
                                                                                                                            Zm
                                                                                                                            Zn
                                                                                                                            Zda)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1443 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     23)) == (0b010001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       10)) == (0b111100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1442 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1442 <b 1758) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1443 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1758
                                                                                                                              let i3h :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  1)
                                                                                                                              let i3l :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  19
                                                                                                                                  2)
                                                                                                                              let Zm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  3)
                                                                                                                              let R :=
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
                                                                                                                              (decode_SQDMULH_Z_ZZi_H
                                                                                                                                i3h
                                                                                                                                i3l
                                                                                                                                Zm
                                                                                                                                R
                                                                                                                                Zn
                                                                                                                                Zd)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1445 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         15
                                                                                                                                         10)) == (0b111100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1444 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1444 <b 1759) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1445 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1759
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let i2 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      19
                                                                                                                                      2)
                                                                                                                                  let Zm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      3)
                                                                                                                                  let R :=
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
                                                                                                                                  (decode_SQDMULH_Z_ZZi_S
                                                                                                                                    size
                                                                                                                                    i2
                                                                                                                                    Zm
                                                                                                                                    R
                                                                                                                                    Zn
                                                                                                                                    Zd)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1447 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b01000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             15
                                                                                                                                             10)) == (0b111100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1446 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1446 <b 1760) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1447 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1760
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let i1 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          20
                                                                                                                                          1)
                                                                                                                                      let Zm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
                                                                                                                                      let R :=
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
                                                                                                                                      (decode_SQDMULH_Z_ZZi_D
                                                                                                                                        size
                                                                                                                                        i1
                                                                                                                                        Zm
                                                                                                                                        R
                                                                                                                                        Zn
                                                                                                                                        Zd)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1449 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   10)) == (0b111010#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1448 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1448 <b 1761) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1449 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1761
                                                                                                                                          let tszh :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let tszl :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              19
                                                                                                                                              2)
                                                                                                                                          let imm3 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              3)
                                                                                                                                          let R :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              11
                                                                                                                                              1)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              10
                                                                                                                                              1)
                                                                                                                                          let Zn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let Zda :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_SRSRA_Z_ZI__
                                                                                                                                            tszh
                                                                                                                                            tszl
                                                                                                                                            imm3
                                                                                                                                            R
                                                                                                                                            U
                                                                                                                                            Zn
                                                                                                                                            Zda)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1451 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       21
                                                                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       10)) == (0b111000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1450 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1450 <b 1762) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1451 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1762
                                                                                                                                              let tszh :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
                                                                                                                                              let tszl :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  19
                                                                                                                                                  2)
                                                                                                                                              let imm3 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  3)
                                                                                                                                              let R :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  11
                                                                                                                                                  1)
                                                                                                                                              let U :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  10
                                                                                                                                                  1)
                                                                                                                                              let Zn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let Zda :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              (decode_SSRA_Z_ZI__
                                                                                                                                                tszh
                                                                                                                                                tszl
                                                                                                                                                imm3
                                                                                                                                                R
                                                                                                                                                U
                                                                                                                                                Zn
                                                                                                                                                Zda)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__1453 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           21
                                                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           15
                                                                                                                                                           10)) == (0b111011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__1452 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__1452 <b 1763) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__1453 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1763
                                                                                                                                                  let tszh :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      2)
                                                                                                                                                  let tszl :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      19
                                                                                                                                                      2)
                                                                                                                                                  let imm3 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      3)
                                                                                                                                                  let R :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      11
                                                                                                                                                      1)
                                                                                                                                                  let U :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      10
                                                                                                                                                      1)
                                                                                                                                                  let Zn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let Zda :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_URSRA_Z_ZI__
                                                                                                                                                    tszh
                                                                                                                                                    tszl
                                                                                                                                                    imm3
                                                                                                                                                    R
                                                                                                                                                    U
                                                                                                                                                    Zn
                                                                                                                                                    Zda)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__1455 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               21
                                                                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               15
                                                                                                                                                               10)) == (0b111001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__1454 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__1454 <b 1764) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__1455 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1764
                                                                                                                                                      let tszh :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          2)
                                                                                                                                                      let tszl :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          19
                                                                                                                                                          2)
                                                                                                                                                      let imm3 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          3)
                                                                                                                                                      let R :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          11
                                                                                                                                                          1)
                                                                                                                                                      let U :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          10
                                                                                                                                                          1)
                                                                                                                                                      let Zn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let Zda :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_USRA_Z_ZI__
                                                                                                                                                        tszh
                                                                                                                                                        tszl
                                                                                                                                                        imm3
                                                                                                                                                        R
                                                                                                                                                        U
                                                                                                                                                        Zn
                                                                                                                                                        Zda)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__1457 ← (( do
                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               31
                                                                                                                                                               10)) == (0b0100010100100010111001#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__1456 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__1456 <b 1765) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__1457 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1765
                                                                                                                                                          let size :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              2)
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
                                                                                                                                                          (decode_AESD_Z_ZZ__
                                                                                                                                                            size
                                                                                                                                                            Zm
                                                                                                                                                            Zdn)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__1459 ← (( do
                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   31
                                                                                                                                                                   10)) == (0b0100010100100010111000#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__1458 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__1458 <b 1766) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__1459 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 1766
                                                                                                                                                              let size :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  22
                                                                                                                                                                  2)
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
                                                                                                                                                              (decode_AESE_Z_ZZ__
                                                                                                                                                                size
                                                                                                                                                                Zm
                                                                                                                                                                Zdn)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__1461 ← (( do
                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       31
                                                                                                                                                                       5)) == (0b010001010010000011100100000#27 : (BitVec 27))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__1460 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__1460 <b 1767) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__1461 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 1767
                                                                                                                                                                  let size :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      2)
                                                                                                                                                                  let Zdn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      5)
                                                                                                                                                                  (decode_AESIMC_Z_Z__
                                                                                                                                                                    size
                                                                                                                                                                    Zdn)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__1463 ← (( do
                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 27) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           31
                                                                                                                                                                           5)) == (0b010001010010000011100000000#27 : (BitVec 27))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__1462 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__1462 <b 1768) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__1463 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 1768
                                                                                                                                                                      let size :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          22
                                                                                                                                                                          2)
                                                                                                                                                                      let Zdn :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          0
                                                                                                                                                                          5)
                                                                                                                                                                      (decode_AESMC_Z_Z__
                                                                                                                                                                        size
                                                                                                                                                                        Zdn)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__1465 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 21)) == (0b01000101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 15
                                                                                                                                                                                 10)) == (0b111101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__1464 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__1464 <b 1769) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__1465 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 1769
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
                                                                                                                                                                          (decode_RAX1_Z_ZZ__
                                                                                                                                                                            size
                                                                                                                                                                            Zm
                                                                                                                                                                            Zn
                                                                                                                                                                            Zd)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
