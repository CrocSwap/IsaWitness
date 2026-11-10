import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0980
import ArmFull.Fn.M0981
import ArmFull.Fn.M0982
import ArmFull.Fn.M1315

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
def __DecodeA64_SVE__seg19 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1547 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 15 10)) == (0b111001#6 : (BitVec 6))))) : Bool) : Bool)
    then
      (do
        let w__1546 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1546 <b 1810) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1547 : Bool)
  then
    (do
      writeReg SEE 1810
      let size := (BitVec.slice __opcode 22 2)
      let Zm := (BitVec.slice __opcode 16 5)
      let H := (BitVec.slice __opcode 10 1)
      let Zn := (BitVec.slice __opcode 5 5)
      let Zd := (BitVec.slice __opcode 0 5)
      (decode_ZIPQ2_Z_ZZ__ size Zm H Zn Zd)
      (pure false))
  else
    (do
      let w__1549 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                 __opcode 21 13)) == (0b011110001#9 : (BitVec 9)))) : Bool) : Bool)
        then
          (do
            let w__1548 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1548 <b 1811) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1549 : Bool)
      then
        (do
          writeReg SEE 1811
          let size := (BitVec.slice __opcode 22 2)
          let Pg := (BitVec.slice __opcode 10 3)
          let Zn := (BitVec.slice __opcode 5 5)
          let Vd := (BitVec.slice __opcode 0 5)
          (decode_ANDQV_Z_P_Z__ size Pg Zn Vd)
          (pure false))
      else
        (do
          let w__1551 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                     __opcode 21 13)) == (0b011101001#9 : (BitVec 9)))) : Bool) : Bool)
            then
              (do
                let w__1550 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1550 <b 1812) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1551 : Bool)
          then
            (do
              writeReg SEE 1812
              let size := (BitVec.slice __opcode 22 2)
              let Pg := (BitVec.slice __opcode 10 3)
              let Zn := (BitVec.slice __opcode 5 5)
              let Vd := (BitVec.slice __opcode 0 5)
              (decode_EORQV_Z_P_Z__ size Pg Zn Vd)
              (pure false))
          else
            (do
              let w__1553 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                         __opcode 21 13)) == (0b011100001#9 : (BitVec 9)))) : Bool) : Bool)
                then
                  (do
                    let w__1552 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1552 <b 1813) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1553 : Bool)
              then
                (do
                  writeReg SEE 1813
                  let size := (BitVec.slice __opcode 22 2)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let Vd := (BitVec.slice __opcode 0 5)
                  (decode_ORQV_Z_P_Z__ size Pg Zn Vd)
                  (pure false))
              else
                (do
                  let w__1555 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                             __opcode 21 13)) == (0b000101001#9 : (BitVec 9)))) : Bool) : Bool)
                    then
                      (do
                        let w__1554 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1554 <b 1814) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1555 : Bool)
                  then
                    (do
                      writeReg SEE 1814
                      let size := (BitVec.slice __opcode 22 2)
                      let U := (BitVec.slice __opcode 16 1)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let Vd := (BitVec.slice __opcode 0 5)
                      (decode_ADDQV_Z_P_Z__ size U Pg Zn Vd)
                      (pure false))
                  else
                    (do
                      let w__1557 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                 __opcode 21 13)) == (0b001100001#9 : (BitVec 9)))) : Bool) : Bool)
                        then
                          (do
                            let w__1556 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1556 <b 1815) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1557 : Bool)
                      then
                        (do
                          writeReg SEE 1815
                          let size := (BitVec.slice __opcode 22 2)
                          let U := (BitVec.slice __opcode 16 1)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let Vd := (BitVec.slice __opcode 0 5)
                          (decode_SMAXQV_Z_P_Z__ size U Pg Zn Vd)
                          (pure false))
                      else
                        (do
                          let w__1559 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                     __opcode 21 13)) == (0b001101001#9 : (BitVec 9)))) : Bool) : Bool)
                            then
                              (do
                                let w__1558 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1558 <b 1816) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1559 : Bool)
                          then
                            (do
                              writeReg SEE 1816
                              let size := (BitVec.slice __opcode 22 2)
                              let U := (BitVec.slice __opcode 16 1)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let Vd := (BitVec.slice __opcode 0 5)
                              (decode_UMAXQV_Z_P_Z__ size U Pg Zn Vd)
                              (pure false))
                          else
                            (do
                              let w__1561 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 21 13)) == (0b001110001#9 : (BitVec 9)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1560 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1560 <b 1817) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1561 : Bool)
                              then
                                (do
                                  writeReg SEE 1817
                                  let size := (BitVec.slice __opcode 22 2)
                                  let U := (BitVec.slice __opcode 16 1)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Zn := (BitVec.slice __opcode 5 5)
                                  let Vd := (BitVec.slice __opcode 0 5)
                                  (decode_SMINQV_Z_P_Z__ size U Pg Zn Vd)
                                  (pure false))
                              else
                                (do
                                  let w__1563 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 21 13)) == (0b001111001#9 : (BitVec 9)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1562 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1562 <b 1818) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1563 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1818
                                      let size := (BitVec.slice __opcode 22 2)
                                      let U := (BitVec.slice __opcode 16 1)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let Vd := (BitVec.slice __opcode 0 5)
                                      (decode_UMINQV_Z_P_Z__ size U Pg Zn Vd)
                                      (pure false))
                                  else
                                    (do
                                      let w__1565 ← (( do
                                        if ((((Sail.BitVec.castWidth (m := 23) (Sail.BitVec.extractLsb
                                               __opcode 31 9)) == (0b00000101001010110011100#23 : (BitVec 23))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1564 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1564 <b 1819) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1565 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1819
                                          let Pn := (BitVec.slice __opcode 5 4)
                                          let Zd := (BitVec.slice __opcode 0 5)
                                          (decode_PMOV_Z_PI_B Pn Zd)
                                          (pure false))
                                      else
                                        (do
                                          let w__1567 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                     __opcode 31 18)) == (0b00000101001011#14 : (BitVec 14))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 16 9)) == (0x9C#8 : (BitVec 8)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1566 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1566 <b 1820) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1567 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1820
                                              let i1 := (BitVec.slice __opcode 17 1)
                                              let Pn := (BitVec.slice __opcode 5 4)
                                              let Zd := (BitVec.slice __opcode 0 5)
                                              (decode_PMOV_Z_PI_H i1 Pn Zd)
                                              (pure false))
                                          else
                                            (do
                                              let w__1569 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                         __opcode 31 19)) == (0b0000010101101#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 16 9)) == (0x9C#8 : (BitVec 8)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1568 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1568 <b 1821) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1569 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1821
                                                  let i2 := (BitVec.slice __opcode 17 2)
                                                  let Pn := (BitVec.slice __opcode 5 4)
                                                  let Zd := (BitVec.slice __opcode 0 5)
                                                  (decode_PMOV_Z_PI_S i2 Pn Zd)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1571 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b000001011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                               __opcode 21 19)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                               __opcode 16 9)) == (0x9C#8 : (BitVec 8))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1570 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1570 <b 1822) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1571 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1822
                                                      let i3h := (BitVec.slice __opcode 22 1)
                                                      let i3l := (BitVec.slice __opcode 17 2)
                                                      let Pn := (BitVec.slice __opcode 5 4)
                                                      let Zd := (BitVec.slice __opcode 0 5)
                                                      (decode_PMOV_Z_PI_D i3h i3l Pn Zd)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1573 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                 __opcode 31 10)) == (0b0000010100101010001110#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1572 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1572 <b 1823) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1573 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1823
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let Pd := (BitVec.slice __opcode 0 4)
                                                          (decode_PMOV_P_ZI_B Zn Pd)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1575 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                     __opcode 31 18)) == (0b00000101001011#14 : (BitVec 14))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                       __opcode 16 10)) == (0b0001110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1574 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1574 <b 1824) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1575 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1824
                                                              let i1 := (BitVec.slice __opcode 17 1)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let Pd := (BitVec.slice __opcode 0 4)
                                                              (decode_PMOV_P_ZI_H i1 Zn Pd)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1577 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                         __opcode 31 19)) == (0b0000010101101#13 : (BitVec 13))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                           __opcode 16 10)) == (0b0001110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1576 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1576 <b 1825) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1577 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1825
                                                                  let i2 :=
                                                                    (BitVec.slice __opcode 17 2)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Pd :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_PMOV_P_ZI_S i2 Zn Pd)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1579 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b000001011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 21 19)) == (0b101#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                 __opcode 16 10)) == (0b0001110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1578 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1578 <b 1826) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1579 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1826
                                                                      let i3h :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let i3l :=
                                                                        (BitVec.slice __opcode 17 2)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Pd :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_PMOV_P_ZI_D i3h i3l Zn
                                                                        Pd)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1581 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 10)) == (0x81C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1580 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1580 <b 1827) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1581 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1827
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let imm2 :=
                                                                            (BitVec.slice __opcode 8
                                                                              2)
                                                                          let PNn :=
                                                                            (BitVec.slice __opcode 5
                                                                              3)
                                                                          let Pd :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_PEXT_PN_RR__ size
                                                                            imm2 PNn Pd)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1583 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                       __opcode 21 9)) == (0b1000000111010#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1582 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1582 <b 1828) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1583 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1828
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let i1 :=
                                                                                (BitVec.slice
                                                                                  __opcode 8 1)
                                                                              let PNn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 3)
                                                                              let Pd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_PEXT_PP_RR__
                                                                                size i1 PNn Pd)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1585 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                         __opcode 21
                                                                                         3)) == (0b1000000111100000010#19 : (BitVec 19)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1584 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1584 <b 1829) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1585 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1829
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let PNd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 3)
                                                                                  (decode_PTRUE_PN_I__
                                                                                    size PNd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1587 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 11)) == (0b10000010000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               9 9)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1586 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1586 <b 1830) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1587 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1830
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let vl :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 1)
                                                                                      let PNn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          4)
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_CNTP_R_PN__
                                                                                        size vl PNn
                                                                                        Rd)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1589 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     14)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       12
                                                                                                       10)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       4
                                                                                                       3)) == (0b10#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1588 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1588 <b 1831) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1589 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1831
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let vl :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 1)
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
                                                                                          let eq :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              3 1)
                                                                                          let PNd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 3)
                                                                                          (decode_WHILELO_PN_RR__
                                                                                            size Rm
                                                                                            vl U lt
                                                                                            Rn eq
                                                                                            PNd)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1591 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         14)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           12
                                                                                                           10)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           4
                                                                                                           3)) == (0b11#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1590 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1590 <b 1832) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1591 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1832
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
                                                                                              let vl :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  1)
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
                                                                                              let eq :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  3
                                                                                                  1)
                                                                                              let PNd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  3)
                                                                                              (decode_WHILELS_PN_RR__
                                                                                                size
                                                                                                Rm
                                                                                                vl U
                                                                                                lt
                                                                                                Rn
                                                                                                eq
                                                                                                PNd)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1593 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             14)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               12
                                                                                                               10)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               4
                                                                                                               3)) == (0b10#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1592 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1592 <b 1833) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1593 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1833
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
                                                                                                  let vl :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      13
                                                                                                      1)
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
                                                                                                  let eq :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      3
                                                                                                      1)
                                                                                                  let PNd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      3)
                                                                                                  (decode_WHILELT_PN_RR__
                                                                                                    size
                                                                                                    Rm
                                                                                                    vl
                                                                                                    U
                                                                                                    lt
                                                                                                    Rn
                                                                                                    eq
                                                                                                    PNd)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1595 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 14)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   12
                                                                                                                   10)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   4
                                                                                                                   3)) == (0b11#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1594 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1594 <b 1834) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1595 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1834
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
                                                                                                      let vl :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          1)
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
                                                                                                      let eq :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          3
                                                                                                          1)
                                                                                                      let PNd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          3)
                                                                                                      (decode_WHILELE_PN_RR__
                                                                                                        size
                                                                                                        Rm
                                                                                                        vl
                                                                                                        U
                                                                                                        lt
                                                                                                        Rn
                                                                                                        eq
                                                                                                        PNd)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1597 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     14)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       12
                                                                                                                       10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       4
                                                                                                                       3)) == (0b11#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1596 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1596 <b 1835) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1597 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1835
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
                                                                                                          let vl :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              1)
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
                                                                                                          let eq :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              3
                                                                                                              1)
                                                                                                          let PNd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              3)
                                                                                                          (decode_WHILEHI_PN_RR__
                                                                                                            size
                                                                                                            Rm
                                                                                                            vl
                                                                                                            U
                                                                                                            lt
                                                                                                            Rn
                                                                                                            eq
                                                                                                            PNd)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1599 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         14)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           12
                                                                                                                           10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           4
                                                                                                                           3)) == (0b10#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1598 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1598 <b 1836) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1599 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1836
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
                                                                                                              let vl :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  1)
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
                                                                                                              let eq :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  3
                                                                                                                  1)
                                                                                                              let PNd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  3)
                                                                                                              (decode_WHILEHS_PN_RR__
                                                                                                                size
                                                                                                                Rm
                                                                                                                vl
                                                                                                                U
                                                                                                                lt
                                                                                                                Rn
                                                                                                                eq
                                                                                                                PNd)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1601 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             14)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               12
                                                                                                                               10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               4
                                                                                                                               3)) == (0b11#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1600 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1600 <b 1837) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1601 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1837
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
                                                                                                                  let vl :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      1)
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
                                                                                                                  let eq :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      3
                                                                                                                      1)
                                                                                                                  let PNd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      3)
                                                                                                                  (decode_WHILEGT_PN_RR__
                                                                                                                    size
                                                                                                                    Rm
                                                                                                                    vl
                                                                                                                    U
                                                                                                                    lt
                                                                                                                    Rn
                                                                                                                    eq
                                                                                                                    PNd)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1603 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 15
                                                                                                                                 14)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   12
                                                                                                                                   10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   4
                                                                                                                                   3)) == (0b10#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1602 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1602 <b 1838) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1603 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1838
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
                                                                                                                      let vl :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          13
                                                                                                                          1)
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
                                                                                                                      let eq :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          3
                                                                                                                          1)
                                                                                                                      let PNd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          3)
                                                                                                                      (decode_WHILEGE_PN_RR__
                                                                                                                        size
                                                                                                                        Rm
                                                                                                                        vl
                                                                                                                        U
                                                                                                                        lt
                                                                                                                        Rn
                                                                                                                        eq
                                                                                                                        PNd)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1605 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 23)) == (0b100001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1604 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1604 <b 1839) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1605 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1839
                                                                                                                          let xs :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              14
                                                                                                                              1)
                                                                                                                          let ff :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              1)
                                                                                                                          let Pg :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              3)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let Zt :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          (decode_LD1B_Z_P_BZ_S_x32_unscaled
                                                                                                                            xs
                                                                                                                            Zm
                                                                                                                            U
                                                                                                                            ff
                                                                                                                            Pg
                                                                                                                            Rn
                                                                                                                            Zt)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1607 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     23)) == (0b100001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       13)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1606 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1606 <b 1840) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1607 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1840
                                                                                                                              let xs :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  1)
                                                                                                                              let Zm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  5)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  14
                                                                                                                                  1)
                                                                                                                              let ff :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  13
                                                                                                                                  1)
                                                                                                                              let Pg :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  3)
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let Zt :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              (decode_LD1SB_Z_P_BZ_S_x32_unscaled
                                                                                                                                xs
                                                                                                                                Zm
                                                                                                                                U
                                                                                                                                ff
                                                                                                                                Pg
                                                                                                                                Rn
                                                                                                                                Zt)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1609 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         23)) == (0b100001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1608 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1608 <b 1841) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1609 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1841
                                                                                                                                  let xs :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      1)
                                                                                                                                  let Zm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let U :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      14
                                                                                                                                      1)
                                                                                                                                  let ff :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      13
                                                                                                                                      1)
                                                                                                                                  let Pg :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      3)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let Zt :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  (decode_LDFF1B_Z_P_BZ_S_x32_unscaled
                                                                                                                                    xs
                                                                                                                                    Zm
                                                                                                                                    U
                                                                                                                                    ff
                                                                                                                                    Pg
                                                                                                                                    Rn
                                                                                                                                    Zt)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1611 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             23)) == (0b100001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               13)) == (0b001#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1610 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1610 <b 1842) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1611 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1842
                                                                                                                                      let xs :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          1)
                                                                                                                                      let Zm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          14
                                                                                                                                          1)
                                                                                                                                      let ff :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          13
                                                                                                                                          1)
                                                                                                                                      let Pg :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          3)
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let Zt :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      (decode_LDFF1SB_Z_P_BZ_S_x32_unscaled
                                                                                                                                        xs
                                                                                                                                        Zm
                                                                                                                                        U
                                                                                                                                        ff
                                                                                                                                        Pg
                                                                                                                                        Rn
                                                                                                                                        Zt)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1613 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 23)) == (0b100001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1612 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1612 <b 1843) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1613 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1843
                                                                                                                                          let xs :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              1)
                                                                                                                                          let Zm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              5)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              14
                                                                                                                                              1)
                                                                                                                                          let ff :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              13
                                                                                                                                              1)
                                                                                                                                          let Pg :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              10
                                                                                                                                              3)
                                                                                                                                          let Rn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let Zt :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_LD1H_Z_P_BZ_S_x32_unscaled
                                                                                                                                            xs
                                                                                                                                            Zm
                                                                                                                                            U
                                                                                                                                            ff
                                                                                                                                            Pg
                                                                                                                                            Rn
                                                                                                                                            Zt)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1615 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     23)) == (0b100001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       21
                                                                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       13)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1614 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1614 <b 1844) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1615 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1844
                                                                                                                                              let xs :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  1)
                                                                                                                                              let Zm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  5)
                                                                                                                                              let U :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  14
                                                                                                                                                  1)
                                                                                                                                              let ff :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  13
                                                                                                                                                  1)
                                                                                                                                              let Pg :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  10
                                                                                                                                                  3)
                                                                                                                                              let Rn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let Zt :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              (decode_LD1SH_Z_P_BZ_S_x32_unscaled
                                                                                                                                                xs
                                                                                                                                                Zm
                                                                                                                                                U
                                                                                                                                                ff
                                                                                                                                                Pg
                                                                                                                                                Rn
                                                                                                                                                Zt)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__1617 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         23)) == (0b100001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           21
                                                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           15
                                                                                                                                                           13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__1616 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__1616 <b 1845) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__1617 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1845
                                                                                                                                                  let xs :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      1)
                                                                                                                                                  let Zm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      5)
                                                                                                                                                  let U :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      14
                                                                                                                                                      1)
                                                                                                                                                  let ff :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      13
                                                                                                                                                      1)
                                                                                                                                                  let Pg :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      10
                                                                                                                                                      3)
                                                                                                                                                  let Rn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let Zt :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_LDFF1H_Z_P_BZ_S_x32_unscaled
                                                                                                                                                    xs
                                                                                                                                                    Zm
                                                                                                                                                    U
                                                                                                                                                    ff
                                                                                                                                                    Pg
                                                                                                                                                    Rn
                                                                                                                                                    Zt)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__1619 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             23)) == (0b100001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               21
                                                                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               15
                                                                                                                                                               13)) == (0b001#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__1618 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__1618 <b 1846) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__1619 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1846
                                                                                                                                                      let xs :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          1)
                                                                                                                                                      let Zm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          5)
                                                                                                                                                      let U :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          14
                                                                                                                                                          1)
                                                                                                                                                      let ff :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          13
                                                                                                                                                          1)
                                                                                                                                                      let Pg :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          10
                                                                                                                                                          3)
                                                                                                                                                      let Rn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let Zt :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_LDFF1SH_Z_P_BZ_S_x32_unscaled
                                                                                                                                                        xs
                                                                                                                                                        Zm
                                                                                                                                                        U
                                                                                                                                                        ff
                                                                                                                                                        Pg
                                                                                                                                                        Rn
                                                                                                                                                        Zt)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__1621 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 23)) == (0b100001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   21
                                                                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   15
                                                                                                                                                                   13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__1620 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__1620 <b 1847) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__1621 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1847
                                                                                                                                                          let xs :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              1)
                                                                                                                                                          let Zm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              5)
                                                                                                                                                          let U :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              14
                                                                                                                                                              1)
                                                                                                                                                          let ff :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              13
                                                                                                                                                              1)
                                                                                                                                                          let Pg :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              3)
                                                                                                                                                          let Rn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              5)
                                                                                                                                                          let Zt :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          (decode_LD1W_Z_P_BZ_S_x32_unscaled
                                                                                                                                                            xs
                                                                                                                                                            Zm
                                                                                                                                                            U
                                                                                                                                                            ff
                                                                                                                                                            Pg
                                                                                                                                                            Rn
                                                                                                                                                            Zt)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
