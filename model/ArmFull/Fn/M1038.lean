import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0969
import ArmFull.Fn.M0970
import ArmFull.Fn.M0971

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
def __DecodeA64_SVE__seg15 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1245 ← (( do
    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
             __opcode 15 12)) == (0x6#4 : (BitVec 4)))) : Bool) : Bool)
    then
      (do
        let w__1244 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1244 <b 1659) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1245 : Bool)
  then
    (do
      writeReg SEE 1659
      let size := (BitVec.slice __opcode 22 2)
      let i1 := (BitVec.slice __opcode 20 1)
      let Zm := (BitVec.slice __opcode 16 4)
      let rot := (BitVec.slice __opcode 10 2)
      let Zn := (BitVec.slice __opcode 5 5)
      let Zda := (BitVec.slice __opcode 0 5)
      (decode_CMLA_Z_ZZZi_S size i1 Zm rot Zn Zda)
      (pure false))
  else
    (do
      let w__1247 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 15 12)) == (0x3#4 : (BitVec 4))))) : Bool) : Bool)
        then
          (do
            let w__1246 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1246 <b 1660) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1247 : Bool)
      then
        (do
          writeReg SEE 1660
          let size := (BitVec.slice __opcode 22 2)
          let Zm := (BitVec.slice __opcode 16 5)
          let rot := (BitVec.slice __opcode 10 2)
          let Zn := (BitVec.slice __opcode 5 5)
          let Zda := (BitVec.slice __opcode 0 5)
          (decode_SQRDCMLAH_Z_ZZZ__ size Zm rot Zn Zda)
          (pure false))
      else
        (do
          let w__1249 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                     __opcode 15 12)) == (0x7#4 : (BitVec 4)))) : Bool) : Bool)
            then
              (do
                let w__1248 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1248 <b 1661) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1249 : Bool)
          then
            (do
              writeReg SEE 1661
              let size := (BitVec.slice __opcode 22 2)
              let i2 := (BitVec.slice __opcode 19 2)
              let Zm := (BitVec.slice __opcode 16 3)
              let rot := (BitVec.slice __opcode 10 2)
              let Zn := (BitVec.slice __opcode 5 5)
              let Zda := (BitVec.slice __opcode 0 5)
              (decode_SQRDCMLAH_Z_ZZZi_H size i2 Zm rot Zn Zda)
              (pure false))
          else
            (do
              let w__1251 ← (( do
                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                         __opcode 15 12)) == (0x7#4 : (BitVec 4)))) : Bool) : Bool)
                then
                  (do
                    let w__1250 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1250 <b 1662) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1251 : Bool)
              then
                (do
                  writeReg SEE 1662
                  let size := (BitVec.slice __opcode 22 2)
                  let i1 := (BitVec.slice __opcode 20 1)
                  let Zm := (BitVec.slice __opcode 16 4)
                  let rot := (BitVec.slice __opcode 10 2)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let Zda := (BitVec.slice __opcode 0 5)
                  (decode_SQRDCMLAH_Z_ZZZi_S size i1 Zm rot Zn Zda)
                  (pure false))
              else
                (do
                  let w__1253 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                               __opcode 15 10)) == (0b011000#6 : (BitVec 6))))) : Bool) : Bool)
                    then
                      (do
                        let w__1252 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1252 <b 1663) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1253 : Bool)
                  then
                    (do
                      writeReg SEE 1663
                      let size := (BitVec.slice __opcode 22 2)
                      let Zm := (BitVec.slice __opcode 16 5)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let Zd := (BitVec.slice __opcode 0 5)
                      (decode_MUL_Z_ZZ__ size Zm Zn Zd)
                      (pure false))
                  else
                    (do
                      let w__1255 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b010001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                   __opcode 15 10)) == (0b111110#6 : (BitVec 6))))) : Bool) : Bool)
                        then
                          (do
                            let w__1254 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1254 <b 1664) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1255 : Bool)
                      then
                        (do
                          writeReg SEE 1664
                          let i3h := (BitVec.slice __opcode 22 1)
                          let i3l := (BitVec.slice __opcode 19 2)
                          let Zm := (BitVec.slice __opcode 16 3)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let Zd := (BitVec.slice __opcode 0 5)
                          (decode_MUL_Z_ZZi_H i3h i3l Zm Zn Zd)
                          (pure false))
                      else
                        (do
                          let w__1257 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode
                                     31 21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                     __opcode 15 10)) == (0b111110#6 : (BitVec 6)))) : Bool) : Bool)
                            then
                              (do
                                let w__1256 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1256 <b 1665) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1257 : Bool)
                          then
                            (do
                              writeReg SEE 1665
                              let size := (BitVec.slice __opcode 22 2)
                              let i2 := (BitVec.slice __opcode 19 2)
                              let Zm := (BitVec.slice __opcode 16 3)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let Zd := (BitVec.slice __opcode 0 5)
                              (decode_MUL_Z_ZZi_S size i2 Zm Zn Zd)
                              (pure false))
                          else
                            (do
                              let w__1259 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                         __opcode 15 10)) == (0b111110#6 : (BitVec 6)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1258 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1258 <b 1666) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1259 : Bool)
                              then
                                (do
                                  writeReg SEE 1666
                                  let size := (BitVec.slice __opcode 22 2)
                                  let i1 := (BitVec.slice __opcode 20 1)
                                  let Zm := (BitVec.slice __opcode 16 4)
                                  let Zn := (BitVec.slice __opcode 5 5)
                                  let Zd := (BitVec.slice __opcode 0 5)
                                  (decode_MUL_Z_ZZi_D size i1 Zm Zn Zd)
                                  (pure false))
                              else
                                (do
                                  let w__1261 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b010001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                               __opcode 15 10)) == (0b000010#6 : (BitVec 6))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1260 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1260 <b 1667) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1261 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1667
                                      let i3h := (BitVec.slice __opcode 22 1)
                                      let i3l := (BitVec.slice __opcode 19 2)
                                      let Zm := (BitVec.slice __opcode 16 3)
                                      let S := (BitVec.slice __opcode 10 1)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let Zda := (BitVec.slice __opcode 0 5)
                                      (decode_MLA_Z_ZZZi_H i3h i3l Zm S Zn Zda)
                                      (pure false))
                                  else
                                    (do
                                      let w__1263 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                 __opcode 15 10)) == (0b000010#6 : (BitVec 6)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1262 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1262 <b 1668) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1263 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1668
                                          let size := (BitVec.slice __opcode 22 2)
                                          let i2 := (BitVec.slice __opcode 19 2)
                                          let Zm := (BitVec.slice __opcode 16 3)
                                          let S := (BitVec.slice __opcode 10 1)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let Zda := (BitVec.slice __opcode 0 5)
                                          (decode_MLA_Z_ZZZi_S size i2 Zm S Zn Zda)
                                          (pure false))
                                      else
                                        (do
                                          let w__1265 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                     __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                     __opcode 15 10)) == (0b000010#6 : (BitVec 6)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1264 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1264 <b 1669) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1265 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1669
                                              let size := (BitVec.slice __opcode 22 2)
                                              let i1 := (BitVec.slice __opcode 20 1)
                                              let Zm := (BitVec.slice __opcode 16 4)
                                              let S := (BitVec.slice __opcode 10 1)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zda := (BitVec.slice __opcode 0 5)
                                              (decode_MLA_Z_ZZZi_D size i1 Zm S Zn Zda)
                                              (pure false))
                                          else
                                            (do
                                              let w__1267 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b010001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 15 10)) == (0b000011#6 : (BitVec 6))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1266 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1266 <b 1670) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1267 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1670
                                                  let i3h := (BitVec.slice __opcode 22 1)
                                                  let i3l := (BitVec.slice __opcode 19 2)
                                                  let Zm := (BitVec.slice __opcode 16 3)
                                                  let S := (BitVec.slice __opcode 10 1)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let Zda := (BitVec.slice __opcode 0 5)
                                                  (decode_MLS_Z_ZZZi_H i3h i3l Zm S Zn Zda)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1269 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                             __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                             __opcode 15 10)) == (0b000011#6 : (BitVec 6)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1268 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1268 <b 1671) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1269 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1671
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let i2 := (BitVec.slice __opcode 19 2)
                                                      let Zm := (BitVec.slice __opcode 16 3)
                                                      let S := (BitVec.slice __opcode 10 1)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let Zda := (BitVec.slice __opcode 0 5)
                                                      (decode_MLS_Z_ZZZi_S size i2 Zm S Zn Zda)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1271 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                 __opcode 15 10)) == (0b000011#6 : (BitVec 6)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1270 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1270 <b 1672) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1271 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1672
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let i1 := (BitVec.slice __opcode 20 1)
                                                          let Zm := (BitVec.slice __opcode 16 4)
                                                          let S := (BitVec.slice __opcode 10 1)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let Zda := (BitVec.slice __opcode 0 5)
                                                          (decode_MLS_Z_ZZZi_D size i1 Zm S Zn Zda)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1273 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                       __opcode 15 12)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1272 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1272 <b 1673) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1273 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1673
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let i3h :=
                                                                (BitVec.slice __opcode 19 2)
                                                              let Zm := (BitVec.slice __opcode 16 3)
                                                              let U := (BitVec.slice __opcode 12 1)
                                                              let i3l :=
                                                                (BitVec.slice __opcode 11 1)
                                                              let T := (BitVec.slice __opcode 10 1)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let Zd := (BitVec.slice __opcode 0 5)
                                                              (decode_SMULLB_Z_ZZi_S size i3h Zm U
                                                                i3l T Zn Zd)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1275 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                           __opcode 15 12)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1274 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1274 <b 1674) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1275 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1674
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let i2h :=
                                                                    (BitVec.slice __opcode 20 1)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 12 1)
                                                                  let i2l :=
                                                                    (BitVec.slice __opcode 11 1)
                                                                  let T :=
                                                                    (BitVec.slice __opcode 10 1)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_SMULLB_Z_ZZi_D size i2h Zm
                                                                    U i2l T Zn Zd)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1277 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                             __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                               __opcode 15 12)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 10 10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1276 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1276 <b 1675) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1277 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1675
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let i3h :=
                                                                        (BitVec.slice __opcode 19 2)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 3)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 12 1)
                                                                      let i3l :=
                                                                        (BitVec.slice __opcode 11 1)
                                                                      let T :=
                                                                        (BitVec.slice __opcode 10 1)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_SMULLT_Z_ZZi_S size
                                                                        i3h Zm U i3l T Zn Zd)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1279 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 12)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 10 10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1278 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1278 <b 1676) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1279 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1676
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let i2h :=
                                                                            (BitVec.slice __opcode
                                                                              20 1)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              12 1)
                                                                          let i2l :=
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
                                                                          (decode_SMULLT_Z_ZZi_D
                                                                            size i2h Zm U i2l T Zn
                                                                            Zd)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1281 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       12)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 10
                                                                                       10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1280 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1280 <b 1677) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1281 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1677
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let i3h :=
                                                                                (BitVec.slice
                                                                                  __opcode 19 2)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 3)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 1)
                                                                              let i3l :=
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
                                                                              (decode_UMULLB_Z_ZZi_S
                                                                                size i3h Zm U i3l T
                                                                                Zn Zd)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1283 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 12)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1282 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1282 <b 1678) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1283 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1678
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let i2h :=
                                                                                    (BitVec.slice
                                                                                      __opcode 20 1)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 1)
                                                                                  let i2l :=
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
                                                                                  (decode_UMULLB_Z_ZZi_D
                                                                                    size i2h Zm U
                                                                                    i2l T Zn Zd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1285 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 12)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               10 10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1284 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1284 <b 1679) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1285 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1679
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let i3h :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          19 2)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 3)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 1)
                                                                                      let i3l :=
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
                                                                                      (decode_UMULLT_Z_ZZi_S
                                                                                        size i3h Zm
                                                                                        U i3l T Zn
                                                                                        Zd)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1287 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   12)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   10
                                                                                                   10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1286 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1286 <b 1680) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1287 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1680
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let i2h :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              20 1)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 1)
                                                                                          let i2l :=
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
                                                                                          (decode_UMULLT_Z_ZZi_D
                                                                                            size i2h
                                                                                            Zm U i2l
                                                                                            T Zn Zd)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1289 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       12)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       10
                                                                                                       10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1288 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1288 <b 1681) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1289 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1681
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let i3h :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  19
                                                                                                  2)
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  3)
                                                                                              let S :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  1)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  1)
                                                                                              let i3l :=
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
                                                                                              let Zda :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              (decode_SMLALB_Z_ZZZi_S
                                                                                                size
                                                                                                i3h
                                                                                                Zm S
                                                                                                U
                                                                                                i3l
                                                                                                T Zn
                                                                                                Zda)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1291 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           12)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           10
                                                                                                           10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1290 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1290 <b 1682) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1291 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1682
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      2)
                                                                                                  let i2h :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      20
                                                                                                      1)
                                                                                                  let Zm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let S :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      13
                                                                                                      1)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      1)
                                                                                                  let i2l :=
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
                                                                                                  let Zda :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  (decode_SMLALB_Z_ZZZi_D
                                                                                                    size
                                                                                                    i2h
                                                                                                    Zm
                                                                                                    S
                                                                                                    U
                                                                                                    i2l
                                                                                                    T
                                                                                                    Zn
                                                                                                    Zda)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1293 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               12)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               10
                                                                                                               10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1292 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1292 <b 1683) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1293 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1683
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          2)
                                                                                                      let i3h :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          19
                                                                                                          2)
                                                                                                      let Zm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          3)
                                                                                                      let S :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          1)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          1)
                                                                                                      let i3l :=
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
                                                                                                      let Zda :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      (decode_SMLALT_Z_ZZZi_S
                                                                                                        size
                                                                                                        i3h
                                                                                                        Zm
                                                                                                        S
                                                                                                        U
                                                                                                        i3l
                                                                                                        T
                                                                                                        Zn
                                                                                                        Zda)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1295 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   12)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   10
                                                                                                                   10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1294 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1294 <b 1684) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1295 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1684
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              2)
                                                                                                          let i2h :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              20
                                                                                                              1)
                                                                                                          let Zm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let S :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              1)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              1)
                                                                                                          let i2l :=
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
                                                                                                          let Zda :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          (decode_SMLALT_Z_ZZZi_D
                                                                                                            size
                                                                                                            i2h
                                                                                                            Zm
                                                                                                            S
                                                                                                            U
                                                                                                            i2l
                                                                                                            T
                                                                                                            Zn
                                                                                                            Zda)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1297 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       12)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       10
                                                                                                                       10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1296 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1296 <b 1685) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1297 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1685
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
                                                                                                              let i3h :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  19
                                                                                                                  2)
                                                                                                              let Zm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  3)
                                                                                                              let S :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  1)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  1)
                                                                                                              let i3l :=
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
                                                                                                              let Zda :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              (decode_UMLALB_Z_ZZZi_S
                                                                                                                size
                                                                                                                i3h
                                                                                                                Zm
                                                                                                                S
                                                                                                                U
                                                                                                                i3l
                                                                                                                T
                                                                                                                Zn
                                                                                                                Zda)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1299 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           12)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           10
                                                                                                                           10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1298 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1298 <b 1686) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1299 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1686
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
                                                                                                                  let i2h :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      20
                                                                                                                      1)
                                                                                                                  let Zm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let S :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      1)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      1)
                                                                                                                  let i2l :=
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
                                                                                                                  let Zda :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  (decode_UMLALB_Z_ZZZi_D
                                                                                                                    size
                                                                                                                    i2h
                                                                                                                    Zm
                                                                                                                    S
                                                                                                                    U
                                                                                                                    i2l
                                                                                                                    T
                                                                                                                    Zn
                                                                                                                    Zda)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1301 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               12)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               10
                                                                                                                               10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1300 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1300 <b 1687) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1301 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1687
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let i3h :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          19
                                                                                                                          2)
                                                                                                                      let Zm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          3)
                                                                                                                      let S :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          13
                                                                                                                          1)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          1)
                                                                                                                      let i3l :=
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
                                                                                                                      let Zda :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      (decode_UMLALT_Z_ZZZi_S
                                                                                                                        size
                                                                                                                        i3h
                                                                                                                        Zm
                                                                                                                        S
                                                                                                                        U
                                                                                                                        i3l
                                                                                                                        T
                                                                                                                        Zn
                                                                                                                        Zda)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1303 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   12)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   10
                                                                                                                                   10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1302 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1302 <b 1688) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1303 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1688
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let i2h :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              20
                                                                                                                              1)
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let S :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              1)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              1)
                                                                                                                          let i2l :=
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
                                                                                                                          let Zda :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          (decode_UMLALT_Z_ZZZi_D
                                                                                                                            size
                                                                                                                            i2h
                                                                                                                            Zm
                                                                                                                            S
                                                                                                                            U
                                                                                                                            i2l
                                                                                                                            T
                                                                                                                            Zn
                                                                                                                            Zda)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1305 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       12)) == (0xA#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       10
                                                                                                                                       10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1304 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1304 <b 1689) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1305 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1689
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let i3h :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  19
                                                                                                                                  2)
                                                                                                                              let Zm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  3)
                                                                                                                              let S :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  13
                                                                                                                                  1)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  1)
                                                                                                                              let i3l :=
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
                                                                                                                              let Zda :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              (decode_SMLSLB_Z_ZZZi_S
                                                                                                                                size
                                                                                                                                i3h
                                                                                                                                Zm
                                                                                                                                S
                                                                                                                                U
                                                                                                                                i3l
                                                                                                                                T
                                                                                                                                Zn
                                                                                                                                Zda)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1307 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           12)) == (0xA#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           10
                                                                                                                                           10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1306 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1306 <b 1690) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1307 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1690
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let i2h :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      20
                                                                                                                                      1)
                                                                                                                                  let Zm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let S :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      13
                                                                                                                                      1)
                                                                                                                                  let U :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      1)
                                                                                                                                  let i2l :=
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
                                                                                                                                  let Zda :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  (decode_SMLSLB_Z_ZZZi_D
                                                                                                                                    size
                                                                                                                                    i2h
                                                                                                                                    Zm
                                                                                                                                    S
                                                                                                                                    U
                                                                                                                                    i2l
                                                                                                                                    T
                                                                                                                                    Zn
                                                                                                                                    Zda)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1309 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               12)) == (0xA#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               10
                                                                                                                                               10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1308 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1308 <b 1691) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1309 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1691
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let i3h :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          19
                                                                                                                                          2)
                                                                                                                                      let Zm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          3)
                                                                                                                                      let S :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          13
                                                                                                                                          1)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          12
                                                                                                                                          1)
                                                                                                                                      let i3l :=
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
                                                                                                                                      let Zda :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      (decode_SMLSLT_Z_ZZZi_S
                                                                                                                                        size
                                                                                                                                        i3h
                                                                                                                                        Zm
                                                                                                                                        S
                                                                                                                                        U
                                                                                                                                        i3l
                                                                                                                                        T
                                                                                                                                        Zn
                                                                                                                                        Zda)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1311 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   12)) == (0xA#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   10
                                                                                                                                                   10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1310 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1310 <b 1692) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1311 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1692
                                                                                                                                          let size :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let i2h :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              20
                                                                                                                                              1)
                                                                                                                                          let Zm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let S :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              13
                                                                                                                                              1)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              12
                                                                                                                                              1)
                                                                                                                                          let i2l :=
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
                                                                                                                                          let Zda :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_SMLSLT_Z_ZZZi_D
                                                                                                                                            size
                                                                                                                                            i2h
                                                                                                                                            Zm
                                                                                                                                            S
                                                                                                                                            U
                                                                                                                                            i2l
                                                                                                                                            T
                                                                                                                                            Zn
                                                                                                                                            Zda)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))


end ArmFull.Functions
