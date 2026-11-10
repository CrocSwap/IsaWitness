import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0966
import ArmFull.Fn.M0967
import ArmFull.Fn.M0968
import ArmFull.Fn.M0969

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
def __DecodeA64_SVE__seg14 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1175 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
             __opcode 21 13)) == (0b001010100#9 : (BitVec 9)))) : Bool) : Bool)
    then
      (do
        let w__1174 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1174 <b 1624) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1175 : Bool)
  then
    (do
      writeReg SEE 1624
      let size := (BitVec.slice __opcode 22 2)
      let Q := (BitVec.slice __opcode 19 1)
      let R := (BitVec.slice __opcode 18 1)
      let N := (BitVec.slice __opcode 17 1)
      let U := (BitVec.slice __opcode 16 1)
      let Pg := (BitVec.slice __opcode 10 3)
      let Zm := (BitVec.slice __opcode 5 5)
      let Zdn := (BitVec.slice __opcode 0 5)
      (decode_SQRSHL_Z_P_ZZ__ size Q R N U Pg Zm Zdn)
      (pure false))
  else
    (do
      let w__1177 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                 __opcode 21 13)) == (0b001011100#9 : (BitVec 9)))) : Bool) : Bool)
        then
          (do
            let w__1176 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1176 <b 1625) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1177 : Bool)
      then
        (do
          writeReg SEE 1625
          let size := (BitVec.slice __opcode 22 2)
          let Q := (BitVec.slice __opcode 19 1)
          let R := (BitVec.slice __opcode 18 1)
          let N := (BitVec.slice __opcode 17 1)
          let U := (BitVec.slice __opcode 16 1)
          let Pg := (BitVec.slice __opcode 10 3)
          let Zm := (BitVec.slice __opcode 5 5)
          let Zdn := (BitVec.slice __opcode 0 5)
          (decode_UQRSHL_Z_P_ZZ__ size Q R N U Pg Zm Zdn)
          (pure false))
      else
        (do
          let w__1179 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                     __opcode 21 13)) == (0b001100100#9 : (BitVec 9)))) : Bool) : Bool)
            then
              (do
                let w__1178 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1178 <b 1626) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1179 : Bool)
          then
            (do
              writeReg SEE 1626
              let size := (BitVec.slice __opcode 22 2)
              let Q := (BitVec.slice __opcode 19 1)
              let R := (BitVec.slice __opcode 18 1)
              let N := (BitVec.slice __opcode 17 1)
              let U := (BitVec.slice __opcode 16 1)
              let Pg := (BitVec.slice __opcode 10 3)
              let Zm := (BitVec.slice __opcode 5 5)
              let Zdn := (BitVec.slice __opcode 0 5)
              (decode_SQSHLR_Z_P_ZZ__ size Q R N U Pg Zm Zdn)
              (pure false))
          else
            (do
              let w__1181 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                         __opcode 21 13)) == (0b001101100#9 : (BitVec 9)))) : Bool) : Bool)
                then
                  (do
                    let w__1180 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1180 <b 1627) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1181 : Bool)
              then
                (do
                  writeReg SEE 1627
                  let size := (BitVec.slice __opcode 22 2)
                  let Q := (BitVec.slice __opcode 19 1)
                  let R := (BitVec.slice __opcode 18 1)
                  let N := (BitVec.slice __opcode 17 1)
                  let U := (BitVec.slice __opcode 16 1)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let Zm := (BitVec.slice __opcode 5 5)
                  let Zdn := (BitVec.slice __opcode 0 5)
                  (decode_UQSHLR_Z_P_ZZ__ size Q R N U Pg Zm Zdn)
                  (pure false))
              else
                (do
                  let w__1183 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                             __opcode 21 13)) == (0b000110100#9 : (BitVec 9)))) : Bool) : Bool)
                    then
                      (do
                        let w__1182 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1182 <b 1628) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1183 : Bool)
                  then
                    (do
                      writeReg SEE 1628
                      let size := (BitVec.slice __opcode 22 2)
                      let Q := (BitVec.slice __opcode 19 1)
                      let R := (BitVec.slice __opcode 18 1)
                      let N := (BitVec.slice __opcode 17 1)
                      let U := (BitVec.slice __opcode 16 1)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Zm := (BitVec.slice __opcode 5 5)
                      let Zdn := (BitVec.slice __opcode 0 5)
                      (decode_SRSHLR_Z_P_ZZ__ size Q R N U Pg Zm Zdn)
                      (pure false))
                  else
                    (do
                      let w__1185 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                 __opcode 21 13)) == (0b000111100#9 : (BitVec 9)))) : Bool) : Bool)
                        then
                          (do
                            let w__1184 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1184 <b 1629) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1185 : Bool)
                      then
                        (do
                          writeReg SEE 1629
                          let size := (BitVec.slice __opcode 22 2)
                          let Q := (BitVec.slice __opcode 19 1)
                          let R := (BitVec.slice __opcode 18 1)
                          let N := (BitVec.slice __opcode 17 1)
                          let U := (BitVec.slice __opcode 16 1)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Zm := (BitVec.slice __opcode 5 5)
                          let Zdn := (BitVec.slice __opcode 0 5)
                          (decode_URSHLR_Z_P_ZZ__ size Q R N U Pg Zm Zdn)
                          (pure false))
                      else
                        (do
                          let w__1187 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                     __opcode 21 13)) == (0b001110100#9 : (BitVec 9)))) : Bool) : Bool)
                            then
                              (do
                                let w__1186 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1186 <b 1630) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1187 : Bool)
                          then
                            (do
                              writeReg SEE 1630
                              let size := (BitVec.slice __opcode 22 2)
                              let Q := (BitVec.slice __opcode 19 1)
                              let R := (BitVec.slice __opcode 18 1)
                              let N := (BitVec.slice __opcode 17 1)
                              let U := (BitVec.slice __opcode 16 1)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Zm := (BitVec.slice __opcode 5 5)
                              let Zdn := (BitVec.slice __opcode 0 5)
                              (decode_SQRSHLR_Z_P_ZZ__ size Q R N U Pg Zm Zdn)
                              (pure false))
                          else
                            (do
                              let w__1189 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 21 13)) == (0b001111100#9 : (BitVec 9)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1188 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1188 <b 1631) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1189 : Bool)
                              then
                                (do
                                  writeReg SEE 1631
                                  let size := (BitVec.slice __opcode 22 2)
                                  let Q := (BitVec.slice __opcode 19 1)
                                  let R := (BitVec.slice __opcode 18 1)
                                  let N := (BitVec.slice __opcode 17 1)
                                  let U := (BitVec.slice __opcode 16 1)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Zm := (BitVec.slice __opcode 5 5)
                                  let Zdn := (BitVec.slice __opcode 0 5)
                                  (decode_UQRSHLR_Z_P_ZZ__ size Q R N U Pg Zm Zdn)
                                  (pure false))
                              else
                                (do
                                  let w__1191 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                               __opcode 15 10)) == (0b011000#6 : (BitVec 6))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1190 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1190 <b 1632) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1191 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1632
                                      let size := (BitVec.slice __opcode 22 2)
                                      let Zm := (BitVec.slice __opcode 16 5)
                                      let S := (BitVec.slice __opcode 12 1)
                                      let R := (BitVec.slice __opcode 11 1)
                                      let T := (BitVec.slice __opcode 10 1)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let Zd := (BitVec.slice __opcode 0 5)
                                      (decode_ADDHNB_Z_ZZ__ size Zm S R T Zn Zd)
                                      (pure false))
                                  else
                                    (do
                                      let w__1193 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 15 10)) == (0b011001#6 : (BitVec 6))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1192 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1192 <b 1633) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1193 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1633
                                          let size := (BitVec.slice __opcode 22 2)
                                          let Zm := (BitVec.slice __opcode 16 5)
                                          let S := (BitVec.slice __opcode 12 1)
                                          let R := (BitVec.slice __opcode 11 1)
                                          let T := (BitVec.slice __opcode 10 1)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let Zd := (BitVec.slice __opcode 0 5)
                                          (decode_ADDHNT_Z_ZZ__ size Zm S R T Zn Zd)
                                          (pure false))
                                      else
                                        (do
                                          let w__1195 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 15 10)) == (0b011100#6 : (BitVec 6))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1194 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1194 <b 1634) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1195 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1634
                                              let size := (BitVec.slice __opcode 22 2)
                                              let Zm := (BitVec.slice __opcode 16 5)
                                              let S := (BitVec.slice __opcode 12 1)
                                              let R := (BitVec.slice __opcode 11 1)
                                              let T := (BitVec.slice __opcode 10 1)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zd := (BitVec.slice __opcode 0 5)
                                              (decode_SUBHNB_Z_ZZ__ size Zm S R T Zn Zd)
                                              (pure false))
                                          else
                                            (do
                                              let w__1197 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 15 10)) == (0b011101#6 : (BitVec 6))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1196 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1196 <b 1635) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1197 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1635
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let Zm := (BitVec.slice __opcode 16 5)
                                                  let S := (BitVec.slice __opcode 12 1)
                                                  let R := (BitVec.slice __opcode 11 1)
                                                  let T := (BitVec.slice __opcode 10 1)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let Zd := (BitVec.slice __opcode 0 5)
                                                  (decode_SUBHNT_Z_ZZ__ size Zm S R T Zn Zd)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1199 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 15 10)) == (0b011010#6 : (BitVec 6))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1198 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1198 <b 1636) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1199 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1636
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let Zm := (BitVec.slice __opcode 16 5)
                                                      let S := (BitVec.slice __opcode 12 1)
                                                      let R := (BitVec.slice __opcode 11 1)
                                                      let T := (BitVec.slice __opcode 10 1)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let Zd := (BitVec.slice __opcode 0 5)
                                                      (decode_RADDHNB_Z_ZZ__ size Zm S R T Zn Zd)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1201 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 15 10)) == (0b011011#6 : (BitVec 6))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1200 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1200 <b 1637) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1201 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1637
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let Zm := (BitVec.slice __opcode 16 5)
                                                          let S := (BitVec.slice __opcode 12 1)
                                                          let R := (BitVec.slice __opcode 11 1)
                                                          let T := (BitVec.slice __opcode 10 1)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let Zd := (BitVec.slice __opcode 0 5)
                                                          (decode_RADDHNT_Z_ZZ__ size Zm S R T Zn Zd)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1203 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 15 10)) == (0b011110#6 : (BitVec 6))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1202 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1202 <b 1638) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1203 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1638
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let Zm := (BitVec.slice __opcode 16 5)
                                                              let S := (BitVec.slice __opcode 12 1)
                                                              let R := (BitVec.slice __opcode 11 1)
                                                              let T := (BitVec.slice __opcode 10 1)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let Zd := (BitVec.slice __opcode 0 5)
                                                              (decode_RSUBHNB_Z_ZZ__ size Zm S R T
                                                                Zn Zd)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1205 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 15 10)) == (0b011111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1204 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1204 <b 1639) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1205 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1639
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let S :=
                                                                    (BitVec.slice __opcode 12 1)
                                                                  let R :=
                                                                    (BitVec.slice __opcode 11 1)
                                                                  let T :=
                                                                    (BitVec.slice __opcode 10 1)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_RSUBHNT_Z_ZZ__ size Zm S R
                                                                    T Zn Zd)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1207 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 15 10)) == (0b001100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1206 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1206 <b 1640) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1207 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1640
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 12 1)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 11 1)
                                                                      let T :=
                                                                        (BitVec.slice __opcode 10 1)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_SABDLB_Z_ZZ__ size Zm
                                                                        S U T Zn Zd)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1209 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 10)) == (0b001101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1208 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1208 <b 1641) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1209 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1641
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let S :=
                                                                            (BitVec.slice __opcode
                                                                              12 1)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              11 1)
                                                                          let T :=
                                                                            (BitVec.slice __opcode
                                                                              10 1)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_SABDLT_Z_ZZ__ size
                                                                            Zm S U T Zn Zd)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1211 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       10)) == (0b001110#6 : (BitVec 6))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1210 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1210 <b 1642) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1211 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1642
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 1)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 11 1)
                                                                              let T :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 1)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Zd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_UABDLB_Z_ZZ__
                                                                                size Zm S U T Zn Zd)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1213 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 10)) == (0b001111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1212 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1212 <b 1643) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1213 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1643
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 1)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 11 1)
                                                                                  let T :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 1)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Zd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_UABDLT_Z_ZZ__
                                                                                    size Zm S U T Zn
                                                                                    Zd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1215 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 10)) == (0b000000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1214 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1214 <b 1644) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1215 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1644
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 1)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          11 1)
                                                                                      let T :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 1)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Zd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_SADDLB_Z_ZZ__
                                                                                        size Zm S U
                                                                                        T Zn Zd)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1217 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   10)) == (0b000001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1216 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1216 <b 1645) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1217 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1645
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 1)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              11 1)
                                                                                          let T :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 1)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Zd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_SADDLT_Z_ZZ__
                                                                                            size Zm
                                                                                            S U T Zn
                                                                                            Zd)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1219 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       10)) == (0b000100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1218 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1218 <b 1646) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1219 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1646
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
                                                                                              let S :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  1)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  11
                                                                                                  1)
                                                                                              let T :=
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
                                                                                              (decode_SSUBLB_Z_ZZ__
                                                                                                size
                                                                                                Zm S
                                                                                                U T
                                                                                                Zn
                                                                                                Zd)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1221 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           10)) == (0b000101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1220 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1220 <b 1647) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1221 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1647
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
                                                                                                  let S :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      1)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      11
                                                                                                      1)
                                                                                                  let T :=
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
                                                                                                  (decode_SSUBLT_Z_ZZ__
                                                                                                    size
                                                                                                    Zm
                                                                                                    S
                                                                                                    U
                                                                                                    T
                                                                                                    Zn
                                                                                                    Zd)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1223 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               10)) == (0b000010#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1222 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1222 <b 1648) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1223 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1648
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
                                                                                                      let S :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          1)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          11
                                                                                                          1)
                                                                                                      let T :=
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
                                                                                                      (decode_UADDLB_Z_ZZ__
                                                                                                        size
                                                                                                        Zm
                                                                                                        S
                                                                                                        U
                                                                                                        T
                                                                                                        Zn
                                                                                                        Zd)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1225 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   10)) == (0b000011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1224 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1224 <b 1649) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1225 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1649
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
                                                                                                          let S :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              1)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              11
                                                                                                              1)
                                                                                                          let T :=
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
                                                                                                          (decode_UADDLT_Z_ZZ__
                                                                                                            size
                                                                                                            Zm
                                                                                                            S
                                                                                                            U
                                                                                                            T
                                                                                                            Zn
                                                                                                            Zd)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1227 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       10)) == (0b000110#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1226 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1226 <b 1650) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1227 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1650
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
                                                                                                              let S :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  1)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  11
                                                                                                                  1)
                                                                                                              let T :=
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
                                                                                                              (decode_USUBLB_Z_ZZ__
                                                                                                                size
                                                                                                                Zm
                                                                                                                S
                                                                                                                U
                                                                                                                T
                                                                                                                Zn
                                                                                                                Zd)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1229 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           10)) == (0b000111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1228 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1228 <b 1651) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1229 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1651
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
                                                                                                                  let S :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      1)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      11
                                                                                                                      1)
                                                                                                                  let T :=
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
                                                                                                                  (decode_USUBLT_Z_ZZ__
                                                                                                                    size
                                                                                                                    Zm
                                                                                                                    S
                                                                                                                    U
                                                                                                                    T
                                                                                                                    Zn
                                                                                                                    Zd)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1231 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               10)) == (0b100000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1230 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1230 <b 1652) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1231 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1652
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
                                                                                                                      let S :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          11
                                                                                                                          1)
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
                                                                                                                      (decode_SADDLBT_Z_ZZ__
                                                                                                                        size
                                                                                                                        Zm
                                                                                                                        S
                                                                                                                        tb
                                                                                                                        Zn
                                                                                                                        Zd)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1233 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   10)) == (0b100010#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1232 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1232 <b 1653) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1233 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1653
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
                                                                                                                          let S :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              11
                                                                                                                              1)
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
                                                                                                                          (decode_SSUBLBT_Z_ZZ__
                                                                                                                            size
                                                                                                                            Zm
                                                                                                                            S
                                                                                                                            tb
                                                                                                                            Zn
                                                                                                                            Zd)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1235 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0x45#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       10)) == (0b100011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1234 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1234 <b 1654) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1235 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1654
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
                                                                                                                              let S :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  11
                                                                                                                                  1)
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
                                                                                                                              (decode_SSUBLTB_Z_ZZ__
                                                                                                                                size
                                                                                                                                Zm
                                                                                                                                S
                                                                                                                                tb
                                                                                                                                Zn
                                                                                                                                Zd)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1237 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         24)) == (0x45#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         21
                                                                                                                                         11)) == (0b00000011011#11 : (BitVec 11)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1236 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1236 <b 1655) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1237 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1655
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let rot :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      1)
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
                                                                                                                                  (decode_CADD_Z_ZZ__
                                                                                                                                    size
                                                                                                                                    rot
                                                                                                                                    Zm
                                                                                                                                    Zdn)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1239 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             24)) == (0x45#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             21
                                                                                                                                             11)) == (0b00000111011#11 : (BitVec 11)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1238 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1238 <b 1656) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1239 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1656
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let rot :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          1)
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
                                                                                                                                      (decode_SQCADD_Z_ZZ__
                                                                                                                                        size
                                                                                                                                        rot
                                                                                                                                        Zm
                                                                                                                                        Zdn)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1241 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   12)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1240 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1240 <b 1657) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1241 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1657
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
                                                                                                                                          (decode_CMLA_Z_ZZZ__
                                                                                                                                            size
                                                                                                                                            Zm
                                                                                                                                            rot
                                                                                                                                            Zn
                                                                                                                                            Zda)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1243 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     12)) == (0x6#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1242 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1242 <b 1658) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1243 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1658
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
                                                                                                                                              (decode_CMLA_Z_ZZZi_H
                                                                                                                                                size
                                                                                                                                                i2
                                                                                                                                                Zm
                                                                                                                                                rot
                                                                                                                                                Zn
                                                                                                                                                Zda)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (pure true)))))))))))))))))))))))))))))))))))


end ArmFull.Functions
