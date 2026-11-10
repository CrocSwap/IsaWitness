import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0971
import ArmFull.Fn.M0972
import ArmFull.Fn.M0973
import ArmFull.Fn.M0974

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
def __DecodeA64_SVE__seg16 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1313 ← (( do
    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 15 12)) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
    then
      (do
        let w__1312 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1312 <b 1693) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1313 : Bool)
  then
    (do
      writeReg SEE 1693
      let size := (BitVec.slice __opcode 22 2)
      let i3h := (BitVec.slice __opcode 19 2)
      let Zm := (BitVec.slice __opcode 16 3)
      let S := (BitVec.slice __opcode 13 1)
      let U := (BitVec.slice __opcode 12 1)
      let i3l := (BitVec.slice __opcode 11 1)
      let T := (BitVec.slice __opcode 10 1)
      let Zn := (BitVec.slice __opcode 5 5)
      let Zda := (BitVec.slice __opcode 0 5)
      (decode_UMLSLB_Z_ZZZi_S size i3h Zm S U i3l T Zn Zda)
      (pure false))
  else
    (do
      let w__1315 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 15 12)) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
        then
          (do
            let w__1314 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1314 <b 1694) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1315 : Bool)
      then
        (do
          writeReg SEE 1694
          let size := (BitVec.slice __opcode 22 2)
          let i2h := (BitVec.slice __opcode 20 1)
          let Zm := (BitVec.slice __opcode 16 4)
          let S := (BitVec.slice __opcode 13 1)
          let U := (BitVec.slice __opcode 12 1)
          let i2l := (BitVec.slice __opcode 11 1)
          let T := (BitVec.slice __opcode 10 1)
          let Zn := (BitVec.slice __opcode 5 5)
          let Zda := (BitVec.slice __opcode 0 5)
          (decode_UMLSLB_Z_ZZZi_D size i2h Zm S U i2l T Zn Zda)
          (pure false))
      else
        (do
          let w__1317 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                       __opcode 15 12)) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 10 10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
            then
              (do
                let w__1316 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1316 <b 1695) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1317 : Bool)
          then
            (do
              writeReg SEE 1695
              let size := (BitVec.slice __opcode 22 2)
              let i3h := (BitVec.slice __opcode 19 2)
              let Zm := (BitVec.slice __opcode 16 3)
              let S := (BitVec.slice __opcode 13 1)
              let U := (BitVec.slice __opcode 12 1)
              let i3l := (BitVec.slice __opcode 11 1)
              let T := (BitVec.slice __opcode 10 1)
              let Zn := (BitVec.slice __opcode 5 5)
              let Zda := (BitVec.slice __opcode 0 5)
              (decode_UMLSLT_Z_ZZZi_S size i3h Zm S U i3l T Zn Zda)
              (pure false))
          else
            (do
              let w__1319 ← (( do
                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                           __opcode 15 12)) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 10 10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    let w__1318 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1318 <b 1696) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1319 : Bool)
              then
                (do
                  writeReg SEE 1696
                  let size := (BitVec.slice __opcode 22 2)
                  let i2h := (BitVec.slice __opcode 20 1)
                  let Zm := (BitVec.slice __opcode 16 4)
                  let S := (BitVec.slice __opcode 13 1)
                  let U := (BitVec.slice __opcode 12 1)
                  let i2l := (BitVec.slice __opcode 11 1)
                  let T := (BitVec.slice __opcode 10 1)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let Zda := (BitVec.slice __opcode 0 5)
                  (decode_UMLSLT_Z_ZZZi_D size i2h Zm S U i2l T Zn Zda)
                  (pure false))
              else
                (do
                  let w__1321 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                               __opcode 15 12)) == (0xE#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                    then
                      (do
                        let w__1320 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1320 <b 1697) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1321 : Bool)
                  then
                    (do
                      writeReg SEE 1697
                      let size := (BitVec.slice __opcode 22 2)
                      let i3h := (BitVec.slice __opcode 19 2)
                      let Zm := (BitVec.slice __opcode 16 3)
                      let i3l := (BitVec.slice __opcode 11 1)
                      let T := (BitVec.slice __opcode 10 1)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let Zd := (BitVec.slice __opcode 0 5)
                      (decode_SQDMULLB_Z_ZZi_S size i3h Zm i3l T Zn Zd)
                      (pure false))
                  else
                    (do
                      let w__1323 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31
                                 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                   __opcode 15 12)) == (0xE#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                        then
                          (do
                            let w__1322 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1322 <b 1698) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1323 : Bool)
                      then
                        (do
                          writeReg SEE 1698
                          let size := (BitVec.slice __opcode 22 2)
                          let i2h := (BitVec.slice __opcode 20 1)
                          let Zm := (BitVec.slice __opcode 16 4)
                          let i2l := (BitVec.slice __opcode 11 1)
                          let T := (BitVec.slice __opcode 10 1)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let Zd := (BitVec.slice __opcode 0 5)
                          (decode_SQDMULLB_Z_ZZi_D size i2h Zm i2l T Zn Zd)
                          (pure false))
                      else
                        (do
                          let w__1325 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode
                                     31 21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                       __opcode 15 12)) == (0xE#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 10 10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                            then
                              (do
                                let w__1324 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1324 <b 1699) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1325 : Bool)
                          then
                            (do
                              writeReg SEE 1699
                              let size := (BitVec.slice __opcode 22 2)
                              let i3h := (BitVec.slice __opcode 19 2)
                              let Zm := (BitVec.slice __opcode 16 3)
                              let i3l := (BitVec.slice __opcode 11 1)
                              let T := (BitVec.slice __opcode 10 1)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let Zd := (BitVec.slice __opcode 0 5)
                              (decode_SQDMULLT_Z_ZZi_S size i3h Zm i3l T Zn Zd)
                              (pure false))
                          else
                            (do
                              let w__1327 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                           __opcode 15 12)) == (0xE#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 10 10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1326 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1326 <b 1700) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1327 : Bool)
                              then
                                (do
                                  writeReg SEE 1700
                                  let size := (BitVec.slice __opcode 22 2)
                                  let i2h := (BitVec.slice __opcode 20 1)
                                  let Zm := (BitVec.slice __opcode 16 4)
                                  let i2l := (BitVec.slice __opcode 11 1)
                                  let T := (BitVec.slice __opcode 10 1)
                                  let Zn := (BitVec.slice __opcode 5 5)
                                  let Zd := (BitVec.slice __opcode 0 5)
                                  (decode_SQDMULLT_Z_ZZi_D size i2h Zm i2l T Zn Zd)
                                  (pure false))
                              else
                                (do
                                  let w__1329 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                               __opcode 15 12)) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1328 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1328 <b 1701) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1329 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1701
                                      let size := (BitVec.slice __opcode 22 2)
                                      let i3h := (BitVec.slice __opcode 19 2)
                                      let Zm := (BitVec.slice __opcode 16 3)
                                      let S := (BitVec.slice __opcode 12 1)
                                      let i3l := (BitVec.slice __opcode 11 1)
                                      let T := (BitVec.slice __opcode 10 1)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let Zda := (BitVec.slice __opcode 0 5)
                                      (decode_SQDMLALB_Z_ZZZi_S size i3h Zm S i3l T Zn Zda)
                                      (pure false))
                                  else
                                    (do
                                      let w__1331 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   __opcode 15 12)) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1330 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1330 <b 1702) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1331 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1702
                                          let size := (BitVec.slice __opcode 22 2)
                                          let i2h := (BitVec.slice __opcode 20 1)
                                          let Zm := (BitVec.slice __opcode 16 4)
                                          let S := (BitVec.slice __opcode 12 1)
                                          let i2l := (BitVec.slice __opcode 11 1)
                                          let T := (BitVec.slice __opcode 10 1)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let Zda := (BitVec.slice __opcode 0 5)
                                          (decode_SQDMLALB_Z_ZZZi_D size i2h Zm S i2l T Zn Zda)
                                          (pure false))
                                      else
                                        (do
                                          let w__1333 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                     __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                       __opcode 15 12)) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 10 10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1332 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1332 <b 1703) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1333 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1703
                                              let size := (BitVec.slice __opcode 22 2)
                                              let i3h := (BitVec.slice __opcode 19 2)
                                              let Zm := (BitVec.slice __opcode 16 3)
                                              let S := (BitVec.slice __opcode 12 1)
                                              let i3l := (BitVec.slice __opcode 11 1)
                                              let T := (BitVec.slice __opcode 10 1)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zda := (BitVec.slice __opcode 0 5)
                                              (decode_SQDMLALT_Z_ZZZi_S size i3h Zm S i3l T Zn Zda)
                                              (pure false))
                                          else
                                            (do
                                              let w__1335 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                         __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                           __opcode 15 12)) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 10 10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1334 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1334 <b 1704) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1335 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1704
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let i2h := (BitVec.slice __opcode 20 1)
                                                  let Zm := (BitVec.slice __opcode 16 4)
                                                  let S := (BitVec.slice __opcode 12 1)
                                                  let i2l := (BitVec.slice __opcode 11 1)
                                                  let T := (BitVec.slice __opcode 10 1)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let Zda := (BitVec.slice __opcode 0 5)
                                                  (decode_SQDMLALT_Z_ZZZi_D size i2h Zm S i2l T Zn
                                                    Zda)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1337 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                             __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                               __opcode 15 12)) == (0x3#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1336 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1336 <b 1705) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1337 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1705
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let i3h := (BitVec.slice __opcode 19 2)
                                                      let Zm := (BitVec.slice __opcode 16 3)
                                                      let S := (BitVec.slice __opcode 12 1)
                                                      let i3l := (BitVec.slice __opcode 11 1)
                                                      let T := (BitVec.slice __opcode 10 1)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let Zda := (BitVec.slice __opcode 0 5)
                                                      (decode_SQDMLSLB_Z_ZZZi_S size i3h Zm S i3l T
                                                        Zn Zda)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1339 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                   __opcode 15 12)) == (0x3#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 10 10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1338 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1338 <b 1706) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1339 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1706
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let i2h := (BitVec.slice __opcode 20 1)
                                                          let Zm := (BitVec.slice __opcode 16 4)
                                                          let S := (BitVec.slice __opcode 12 1)
                                                          let i2l := (BitVec.slice __opcode 11 1)
                                                          let T := (BitVec.slice __opcode 10 1)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let Zda := (BitVec.slice __opcode 0 5)
                                                          (decode_SQDMLSLB_Z_ZZZi_D size i2h Zm S
                                                            i2l T Zn Zda)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1341 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b01000100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                       __opcode 15 12)) == (0x3#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 10 10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1340 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1340 <b 1707) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1341 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1707
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let i3h :=
                                                                (BitVec.slice __opcode 19 2)
                                                              let Zm := (BitVec.slice __opcode 16 3)
                                                              let S := (BitVec.slice __opcode 12 1)
                                                              let i3l :=
                                                                (BitVec.slice __opcode 11 1)
                                                              let T := (BitVec.slice __opcode 10 1)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let Zda := (BitVec.slice __opcode 0 5)
                                                              (decode_SQDMLSLT_Z_ZZZi_S size i3h Zm
                                                                S i3l T Zn Zda)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1343 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 31 21)) == (0b01000100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                           __opcode 15 12)) == (0x3#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 10 10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1342 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1342 <b 1708) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1343 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1708
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let i2h :=
                                                                    (BitVec.slice __opcode 20 1)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let S :=
                                                                    (BitVec.slice __opcode 12 1)
                                                                  let i2l :=
                                                                    (BitVec.slice __opcode 11 1)
                                                                  let T :=
                                                                    (BitVec.slice __opcode 10 1)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zda :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_SQDMLSLT_Z_ZZZi_D size i2h
                                                                    Zm S i2l T Zn Zda)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1345 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 15 10)) == (0b000010#6 : (BitVec 6))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1344 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1344 <b 1709) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1345 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1709
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 10 1)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zda :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_SQDMLALBT_Z_ZZZ__ size
                                                                        Zm S Zn Zda)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1347 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 24)) == (0x44#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 10)) == (0b000011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1346 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1346 <b 1710) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1347 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1710
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let S :=
                                                                            (BitVec.slice __opcode
                                                                              10 1)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zda :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_SQDMLSLBT_Z_ZZZ__
                                                                            size Zm S Zn Zda)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1349 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b010001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       10)) == (0b111101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1348 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1348 <b 1711) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1349 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1711
                                                                              let i3h :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let i3l :=
                                                                                (BitVec.slice
                                                                                  __opcode 19 2)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 3)
                                                                              let R :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 1)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Zd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_SQRDMULH_Z_ZZi_H
                                                                                i3h i3l Zm R Zn Zd)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1351 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         10)) == (0b111101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1350 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1350 <b 1712) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1351 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1712
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let i2 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 19 2)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 3)
                                                                                  let R :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 1)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Zd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_SQRDMULH_Z_ZZi_S
                                                                                    size i2 Zm R Zn
                                                                                    Zd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1353 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 21)) == (0b01000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 10)) == (0b111101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1352 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1352 <b 1713) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1353 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1713
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let i1 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          20 1)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let R :=
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
                                                                                      (decode_SQRDMULH_Z_ZZi_D
                                                                                        size i1 Zm R
                                                                                        Zn Zd)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1355 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b010001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   10)) == (0b000100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1354 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1354 <b 1714) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1355 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1714
                                                                                          let i3h :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let i3l :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              19 2)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 3)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 1)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Zda :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_SQRDMLAH_Z_ZZZi_H
                                                                                            i3h i3l
                                                                                            Zm S Zn
                                                                                            Zda)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1357 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     10)) == (0b000100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1356 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1356 <b 1715) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1357 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1715
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
                                                                                              let S :=
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
                                                                                              (decode_SQRDMLAH_Z_ZZZi_S
                                                                                                size
                                                                                                i2
                                                                                                Zm S
                                                                                                Zn
                                                                                                Zda)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1359 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         21)) == (0b01000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         10)) == (0b000100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1358 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1358 <b 1716) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1359 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1716
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
                                                                                                  let S :=
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
                                                                                                  (decode_SQRDMLAH_Z_ZZZi_D
                                                                                                    size
                                                                                                    i1
                                                                                                    Zm
                                                                                                    S
                                                                                                    Zn
                                                                                                    Zda)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1361 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             23)) == (0b010001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               10)) == (0b000101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1360 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1360 <b 1717) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1361 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1717
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
                                                                                                      let S :=
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
                                                                                                      (decode_SQRDMLSH_Z_ZZZi_H
                                                                                                        i3h
                                                                                                        i3l
                                                                                                        Zm
                                                                                                        S
                                                                                                        Zn
                                                                                                        Zda)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1363 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b01000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 10)) == (0b000101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1362 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1362 <b 1718) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1363 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1718
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
                                                                                                          let S :=
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
                                                                                                          (decode_SQRDMLSH_Z_ZZZi_S
                                                                                                            size
                                                                                                            i2
                                                                                                            Zm
                                                                                                            S
                                                                                                            Zn
                                                                                                            Zda)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1365 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     21)) == (0b01000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     10)) == (0b000101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1364 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1364 <b 1719) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1365 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1719
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
                                                                                                              let S :=
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
                                                                                                              (decode_SQRDMLSH_Z_ZZZi_D
                                                                                                                size
                                                                                                                i1
                                                                                                                Zm
                                                                                                                S
                                                                                                                Zn
                                                                                                                Zda)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1367 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         21
                                                                                                                         13)) == (0b010000100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1366 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1366 <b 1720) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1367 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1720
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
                                                                                                                  let R :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      18
                                                                                                                      1)
                                                                                                                  let S :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      17
                                                                                                                      1)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      1)
                                                                                                                  let Pg :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      3)
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
                                                                                                                  (decode_SHADD_Z_P_ZZ__
                                                                                                                    size
                                                                                                                    R
                                                                                                                    S
                                                                                                                    U
                                                                                                                    Pg
                                                                                                                    Zm
                                                                                                                    Zdn)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1369 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             21
                                                                                                                             13)) == (0b010010100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1368 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1368 <b 1721) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1369 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1721
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let R :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          18
                                                                                                                          1)
                                                                                                                      let S :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          17
                                                                                                                          1)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          1)
                                                                                                                      let Pg :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          3)
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
                                                                                                                      (decode_SHSUB_Z_P_ZZ__
                                                                                                                        size
                                                                                                                        R
                                                                                                                        S
                                                                                                                        U
                                                                                                                        Pg
                                                                                                                        Zm
                                                                                                                        Zdn)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1371 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 21
                                                                                                                                 13)) == (0b010110100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1370 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1370 <b 1722) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1371 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1722
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let R :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              18
                                                                                                                              1)
                                                                                                                          let S :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              17
                                                                                                                              1)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              1)
                                                                                                                          let Pg :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              3)
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
                                                                                                                          (decode_SHSUBR_Z_P_ZZ__
                                                                                                                            size
                                                                                                                            R
                                                                                                                            S
                                                                                                                            U
                                                                                                                            Pg
                                                                                                                            Zm
                                                                                                                            Zdn)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1373 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     21
                                                                                                                                     13)) == (0b010100100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1372 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1372 <b 1723) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1373 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1723
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let R :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  18
                                                                                                                                  1)
                                                                                                                              let S :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  17
                                                                                                                                  1)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  1)
                                                                                                                              let Pg :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  3)
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
                                                                                                                              (decode_SRHADD_Z_P_ZZ__
                                                                                                                                size
                                                                                                                                R
                                                                                                                                S
                                                                                                                                U
                                                                                                                                Pg
                                                                                                                                Zm
                                                                                                                                Zdn)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1375 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         21
                                                                                                                                         13)) == (0b010001100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1374 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1374 <b 1724) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1375 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1724
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let R :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      18
                                                                                                                                      1)
                                                                                                                                  let S :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      17
                                                                                                                                      1)
                                                                                                                                  let U :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      1)
                                                                                                                                  let Pg :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      3)
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
                                                                                                                                  (decode_UHADD_Z_P_ZZ__
                                                                                                                                    size
                                                                                                                                    R
                                                                                                                                    S
                                                                                                                                    U
                                                                                                                                    Pg
                                                                                                                                    Zm
                                                                                                                                    Zdn)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1377 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             21
                                                                                                                                             13)) == (0b010011100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1376 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1376 <b 1725) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1377 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1725
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let R :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          18
                                                                                                                                          1)
                                                                                                                                      let S :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          17
                                                                                                                                          1)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          1)
                                                                                                                                      let Pg :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          3)
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
                                                                                                                                      (decode_UHSUB_Z_P_ZZ__
                                                                                                                                        size
                                                                                                                                        R
                                                                                                                                        S
                                                                                                                                        U
                                                                                                                                        Pg
                                                                                                                                        Zm
                                                                                                                                        Zdn)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1379 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 21
                                                                                                                                                 13)) == (0b010111100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1378 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1378 <b 1726) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1379 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1726
                                                                                                                                          let size :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let R :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              18
                                                                                                                                              1)
                                                                                                                                          let S :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              17
                                                                                                                                              1)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              1)
                                                                                                                                          let Pg :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              10
                                                                                                                                              3)
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
                                                                                                                                          (decode_UHSUBR_Z_P_ZZ__
                                                                                                                                            size
                                                                                                                                            R
                                                                                                                                            S
                                                                                                                                            U
                                                                                                                                            Pg
                                                                                                                                            Zm
                                                                                                                                            Zdn)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1381 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     24)) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     21
                                                                                                                                                     13)) == (0b010101100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1380 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1380 <b 1727) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1381 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1727
                                                                                                                                              let size :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
                                                                                                                                              let R :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  18
                                                                                                                                                  1)
                                                                                                                                              let S :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  17
                                                                                                                                                  1)
                                                                                                                                              let U :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  1)
                                                                                                                                              let Pg :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  10
                                                                                                                                                  3)
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
                                                                                                                                              (decode_URHADD_Z_P_ZZ__
                                                                                                                                                size
                                                                                                                                                R
                                                                                                                                                S
                                                                                                                                                U
                                                                                                                                                Pg
                                                                                                                                                Zm
                                                                                                                                                Zdn)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (pure true)))))))))))))))))))))))))))))))))))


end ArmFull.Functions
