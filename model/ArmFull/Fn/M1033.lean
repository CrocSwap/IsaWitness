import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0944
import ArmFull.Fn.M0945
import ArmFull.Fn.M0946

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
def __DecodeA64_SVE__seg6 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__521 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
             __opcode 21 9)) == (0b1010101000100#13 : (BitVec 13)))) : Bool) : Bool)
    then
      (do
        let w__520 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__520 <b 1297) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__521 : Bool)
  then
    (do
      writeReg SEE 1297
      let size := (BitVec.slice __opcode 22 2)
      let D := (BitVec.slice __opcode 17 1)
      let U := (BitVec.slice __opcode 16 1)
      let sf := (BitVec.slice __opcode 10 1)
      let Pm := (BitVec.slice __opcode 5 4)
      let Rdn := (BitVec.slice __opcode 0 5)
      (decode_SQDECP_R_P_R_SX size D U sf Pm Rdn)
      (pure false))
  else
    (do
      let w__523 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                 __opcode 21 9)) == (0b1010111000110#13 : (BitVec 13)))) : Bool) : Bool)
        then
          (do
            let w__522 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__522 <b 1298) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__523 : Bool)
      then
        (do
          writeReg SEE 1298
          let size := (BitVec.slice __opcode 22 2)
          let D := (BitVec.slice __opcode 17 1)
          let U := (BitVec.slice __opcode 16 1)
          let sf := (BitVec.slice __opcode 10 1)
          let Pm := (BitVec.slice __opcode 5 4)
          let Rdn := (BitVec.slice __opcode 0 5)
          (decode_UQDECP_R_P_R_X size D U sf Pm Rdn)
          (pure false))
      else
        (do
          let w__525 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                     __opcode 21 9)) == (0b1010101000110#13 : (BitVec 13)))) : Bool) : Bool)
            then
              (do
                let w__524 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__524 <b 1299) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__525 : Bool)
          then
            (do
              writeReg SEE 1299
              let size := (BitVec.slice __opcode 22 2)
              let D := (BitVec.slice __opcode 17 1)
              let U := (BitVec.slice __opcode 16 1)
              let sf := (BitVec.slice __opcode 10 1)
              let Pm := (BitVec.slice __opcode 5 4)
              let Rdn := (BitVec.slice __opcode 0 5)
              (decode_SQDECP_R_P_R_X size D U sf Pm Rdn)
              (pure false))
          else
            (do
              let w__527 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                         __opcode 21 9)) == (0b1011011000000#13 : (BitVec 13)))) : Bool) : Bool)
                then
                  (do
                    let w__526 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__526 <b 1300) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__527 : Bool)
              then
                (do
                  writeReg SEE 1300
                  let size := (BitVec.slice __opcode 22 2)
                  let D := (BitVec.slice __opcode 16 1)
                  let Pm := (BitVec.slice __opcode 5 4)
                  let Zdn := (BitVec.slice __opcode 0 5)
                  (decode_DECP_Z_P_Z__ size D Pm Zdn)
                  (pure false))
              else
                (do
                  let w__529 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                             __opcode 21 9)) == (0b1011001000000#13 : (BitVec 13)))) : Bool) : Bool)
                    then
                      (do
                        let w__528 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__528 <b 1301) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__529 : Bool)
                  then
                    (do
                      writeReg SEE 1301
                      let size := (BitVec.slice __opcode 22 2)
                      let D := (BitVec.slice __opcode 16 1)
                      let Pm := (BitVec.slice __opcode 5 4)
                      let Zdn := (BitVec.slice __opcode 0 5)
                      (decode_INCP_Z_P_Z__ size D Pm Zdn)
                      (pure false))
                  else
                    (do
                      let w__531 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                 __opcode 21 9)) == (0b1010011000000#13 : (BitVec 13)))) : Bool) : Bool)
                        then
                          (do
                            let w__530 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__530 <b 1302) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__531 : Bool)
                      then
                        (do
                          writeReg SEE 1302
                          let size := (BitVec.slice __opcode 22 2)
                          let D := (BitVec.slice __opcode 17 1)
                          let U := (BitVec.slice __opcode 16 1)
                          let Pm := (BitVec.slice __opcode 5 4)
                          let Zdn := (BitVec.slice __opcode 0 5)
                          (decode_UQINCP_Z_P_Z__ size D U Pm Zdn)
                          (pure false))
                      else
                        (do
                          let w__533 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                     __opcode 21 9)) == (0b1010001000000#13 : (BitVec 13)))) : Bool) : Bool)
                            then
                              (do
                                let w__532 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__532 <b 1303) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__533 : Bool)
                          then
                            (do
                              writeReg SEE 1303
                              let size := (BitVec.slice __opcode 22 2)
                              let D := (BitVec.slice __opcode 17 1)
                              let U := (BitVec.slice __opcode 16 1)
                              let Pm := (BitVec.slice __opcode 5 4)
                              let Zdn := (BitVec.slice __opcode 0 5)
                              (decode_SQINCP_Z_P_Z__ size D U Pm Zdn)
                              (pure false))
                          else
                            (do
                              let w__535 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                         __opcode 21 9)) == (0b1010111000000#13 : (BitVec 13)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__534 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__534 <b 1304) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__535 : Bool)
                              then
                                (do
                                  writeReg SEE 1304
                                  let size := (BitVec.slice __opcode 22 2)
                                  let D := (BitVec.slice __opcode 17 1)
                                  let U := (BitVec.slice __opcode 16 1)
                                  let Pm := (BitVec.slice __opcode 5 4)
                                  let Zdn := (BitVec.slice __opcode 0 5)
                                  (decode_UQDECP_Z_P_Z__ size D U Pm Zdn)
                                  (pure false))
                              else
                                (do
                                  let w__537 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                             __opcode 21 9)) == (0b1010101000000#13 : (BitVec 13)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__536 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__536 <b 1305) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__537 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1305
                                      let size := (BitVec.slice __opcode 22 2)
                                      let D := (BitVec.slice __opcode 17 1)
                                      let U := (BitVec.slice __opcode 16 1)
                                      let Pm := (BitVec.slice __opcode 5 4)
                                      let Zdn := (BitVec.slice __opcode 0 5)
                                      (decode_SQDECP_Z_P_Z__ size D U Pm Zdn)
                                      (pure false))
                                  else
                                    (do
                                      let w__539 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 31 20)) == (0x043#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                 __opcode 15 10)) == (0b111001#6 : (BitVec 6)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__538 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__538 <b 1306) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__539 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1306
                                          let size := (BitVec.slice __opcode 22 2)
                                          let imm4 := (BitVec.slice __opcode 16 4)
                                          let D := (BitVec.slice __opcode 10 1)
                                          let pattern := (BitVec.slice __opcode 5 5)
                                          let Rdn := (BitVec.slice __opcode 0 5)
                                          (decode_DECB_R_RS__ size imm4 D pattern Rdn)
                                          (pure false))
                                      else
                                        (do
                                          let w__541 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 31 20)) == (0x047#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                     __opcode 15 10)) == (0b111001#6 : (BitVec 6)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__540 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__540 <b 1307) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__541 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1307
                                              let size := (BitVec.slice __opcode 22 2)
                                              let imm4 := (BitVec.slice __opcode 16 4)
                                              let D := (BitVec.slice __opcode 10 1)
                                              let pattern := (BitVec.slice __opcode 5 5)
                                              let Rdn := (BitVec.slice __opcode 0 5)
                                              (decode_DECH_R_RS__ size imm4 D pattern Rdn)
                                              (pure false))
                                          else
                                            (do
                                              let w__543 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 31 20)) == (0x04B#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                         __opcode 15 10)) == (0b111001#6 : (BitVec 6)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__542 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__542 <b 1308) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__543 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1308
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let imm4 := (BitVec.slice __opcode 16 4)
                                                  let D := (BitVec.slice __opcode 10 1)
                                                  let pattern := (BitVec.slice __opcode 5 5)
                                                  let Rdn := (BitVec.slice __opcode 0 5)
                                                  (decode_DECW_R_RS__ size imm4 D pattern Rdn)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__545 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 31 20)) == (0x04F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                             __opcode 15 10)) == (0b111001#6 : (BitVec 6)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__544 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__544 <b 1309) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__545 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1309
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let imm4 := (BitVec.slice __opcode 16 4)
                                                      let D := (BitVec.slice __opcode 10 1)
                                                      let pattern := (BitVec.slice __opcode 5 5)
                                                      let Rdn := (BitVec.slice __opcode 0 5)
                                                      (decode_DECD_R_RS__ size imm4 D pattern Rdn)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__547 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0x043#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                 __opcode 15 10)) == (0b111000#6 : (BitVec 6)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__546 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__546 <b 1310) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__547 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1310
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let imm4 := (BitVec.slice __opcode 16 4)
                                                          let D := (BitVec.slice __opcode 10 1)
                                                          let pattern := (BitVec.slice __opcode 5 5)
                                                          let Rdn := (BitVec.slice __opcode 0 5)
                                                          (decode_INCB_R_RS__ size imm4 D pattern
                                                            Rdn)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__549 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0x047#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                     __opcode 15 10)) == (0b111000#6 : (BitVec 6)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__548 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__548 <b 1311) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__549 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1311
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let imm4 :=
                                                                (BitVec.slice __opcode 16 4)
                                                              let D := (BitVec.slice __opcode 10 1)
                                                              let pattern :=
                                                                (BitVec.slice __opcode 5 5)
                                                              let Rdn := (BitVec.slice __opcode 0 5)
                                                              (decode_INCH_R_RS__ size imm4 D
                                                                pattern Rdn)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__551 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 31 20)) == (0x04B#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                         __opcode 15 10)) == (0b111000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__550 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__550 <b 1312) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__551 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1312
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let imm4 :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let D :=
                                                                    (BitVec.slice __opcode 10 1)
                                                                  let pattern :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Rdn :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_INCW_R_RS__ size imm4 D
                                                                    pattern Rdn)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__553 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0x04F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                             __opcode 15 10)) == (0b111000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__552 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__552 <b 1313) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__553 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1313
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let imm4 :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let D :=
                                                                        (BitVec.slice __opcode 10 1)
                                                                      let pattern :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Rdn :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_INCD_R_RS__ size imm4
                                                                        D pattern Rdn)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__555 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 20)) == (0x042#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 10)) == (0b111101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__554 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__554 <b 1314) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__555 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1314
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let sf :=
                                                                            (BitVec.slice __opcode
                                                                              20 1)
                                                                          let imm4 :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              11 1)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              10 1)
                                                                          let pattern :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Rdn :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_UQINCB_R_RS_UW
                                                                            size sf imm4 D U pattern
                                                                            Rdn)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__557 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 20)) == (0x046#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 10)) == (0b111101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__556 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__556 <b 1315) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__557 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1315
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let sf :=
                                                                                (BitVec.slice
                                                                                  __opcode 20 1)
                                                                              let imm4 :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 11 1)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 1)
                                                                              let pattern :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Rdn :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_UQINCH_R_RS_UW
                                                                                size sf imm4 D U
                                                                                pattern Rdn)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__559 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0x04A#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         10)) == (0b111101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__558 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__558 <b 1316) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__559 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1316
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let sf :=
                                                                                    (BitVec.slice
                                                                                      __opcode 20 1)
                                                                                  let imm4 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 11 1)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 1)
                                                                                  let pattern :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Rdn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_UQINCW_R_RS_UW
                                                                                    size sf imm4 D U
                                                                                    pattern Rdn)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__561 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0x04E#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 10)) == (0b111101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__560 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__560 <b 1317) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__561 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1317
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let sf :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          20 1)
                                                                                      let imm4 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          11 1)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 1)
                                                                                      let pattern :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Rdn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_UQINCD_R_RS_UW
                                                                                        size sf imm4
                                                                                        D U pattern
                                                                                        Rdn)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__563 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0x042#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 10)) == (0b111100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__562 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__562 <b 1318) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__563 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1318
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let sf :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              20 1)
                                                                                          let imm4 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              11 1)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 1)
                                                                                          let pattern :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Rdn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_SQINCB_R_RS_SX
                                                                                            size sf
                                                                                            imm4 D U
                                                                                            pattern
                                                                                            Rdn)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__565 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     20)) == (0x046#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     10)) == (0b111100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__564 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__564 <b 1319) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__565 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1319
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let sf :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  20
                                                                                                  1)
                                                                                              let imm4 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let D :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  11
                                                                                                  1)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  1)
                                                                                              let pattern :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let Rdn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              (decode_SQINCH_R_RS_SX
                                                                                                size
                                                                                                sf
                                                                                                imm4
                                                                                                D U
                                                                                                pattern
                                                                                                Rdn)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__567 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         20)) == (0x04A#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         10)) == (0b111100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__566 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__566 <b 1320) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__567 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1320
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      2)
                                                                                                  let sf :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      20
                                                                                                      1)
                                                                                                  let imm4 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      11
                                                                                                      1)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      1)
                                                                                                  let pattern :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let Rdn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  (decode_SQINCW_R_RS_SX
                                                                                                    size
                                                                                                    sf
                                                                                                    imm4
                                                                                                    D
                                                                                                    U
                                                                                                    pattern
                                                                                                    Rdn)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__569 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0x04E#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             10)) == (0b111100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__568 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__568 <b 1321) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__569 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1321
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          2)
                                                                                                      let sf :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          20
                                                                                                          1)
                                                                                                      let imm4 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let D :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          11
                                                                                                          1)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          1)
                                                                                                      let pattern :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let Rdn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      (decode_SQINCD_R_RS_SX
                                                                                                        size
                                                                                                        sf
                                                                                                        imm4
                                                                                                        D
                                                                                                        U
                                                                                                        pattern
                                                                                                        Rdn)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__571 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0x043#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 10)) == (0b111101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__570 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__570 <b 1322) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__571 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1322
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              2)
                                                                                                          let sf :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              20
                                                                                                              1)
                                                                                                          let imm4 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let D :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              11
                                                                                                              1)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              1)
                                                                                                          let pattern :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let Rdn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          (decode_UQINCB_R_RS_X
                                                                                                            size
                                                                                                            sf
                                                                                                            imm4
                                                                                                            D
                                                                                                            U
                                                                                                            pattern
                                                                                                            Rdn)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__573 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0x047#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     10)) == (0b111101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__572 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__572 <b 1323) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__573 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1323
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
                                                                                                              let sf :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  20
                                                                                                                  1)
                                                                                                              let imm4 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let D :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  11
                                                                                                                  1)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  1)
                                                                                                              let pattern :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let Rdn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              (decode_UQINCH_R_RS_X
                                                                                                                size
                                                                                                                sf
                                                                                                                imm4
                                                                                                                D
                                                                                                                U
                                                                                                                pattern
                                                                                                                Rdn)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__575 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0x04B#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         10)) == (0b111101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__574 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__574 <b 1324) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__575 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1324
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
                                                                                                                  let sf :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      20
                                                                                                                      1)
                                                                                                                  let imm4 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let D :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      11
                                                                                                                      1)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      1)
                                                                                                                  let pattern :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let Rdn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  (decode_UQINCW_R_RS_X
                                                                                                                    size
                                                                                                                    sf
                                                                                                                    imm4
                                                                                                                    D
                                                                                                                    U
                                                                                                                    pattern
                                                                                                                    Rdn)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__577 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0x04F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             10)) == (0b111101#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__576 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__576 <b 1325) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__577 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1325
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let sf :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          20
                                                                                                                          1)
                                                                                                                      let imm4 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let D :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          11
                                                                                                                          1)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          1)
                                                                                                                      let pattern :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let Rdn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      (decode_UQINCD_R_RS_X
                                                                                                                        size
                                                                                                                        sf
                                                                                                                        imm4
                                                                                                                        D
                                                                                                                        U
                                                                                                                        pattern
                                                                                                                        Rdn)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__579 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 20)) == (0x043#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 15
                                                                                                                                 10)) == (0b111100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__578 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__578 <b 1326) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__579 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1326
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let sf :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              20
                                                                                                                              1)
                                                                                                                          let imm4 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let D :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              11
                                                                                                                              1)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              1)
                                                                                                                          let pattern :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let Rdn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          (decode_SQINCB_R_RS_X
                                                                                                                            size
                                                                                                                            sf
                                                                                                                            imm4
                                                                                                                            D
                                                                                                                            U
                                                                                                                            pattern
                                                                                                                            Rdn)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__581 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     20)) == (0x047#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     15
                                                                                                                                     10)) == (0b111100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__580 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__580 <b 1327) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__581 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1327
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let sf :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  20
                                                                                                                                  1)
                                                                                                                              let imm4 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let D :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  11
                                                                                                                                  1)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  1)
                                                                                                                              let pattern :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let Rdn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              (decode_SQINCH_R_RS_X
                                                                                                                                size
                                                                                                                                sf
                                                                                                                                imm4
                                                                                                                                D
                                                                                                                                U
                                                                                                                                pattern
                                                                                                                                Rdn)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__583 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         20)) == (0x04B#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         15
                                                                                                                                         10)) == (0b111100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__582 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__582 <b 1328) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__583 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1328
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let sf :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      20
                                                                                                                                      1)
                                                                                                                                  let imm4 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let D :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      11
                                                                                                                                      1)
                                                                                                                                  let U :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      1)
                                                                                                                                  let pattern :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let Rdn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  (decode_SQINCW_R_RS_X
                                                                                                                                    size
                                                                                                                                    sf
                                                                                                                                    imm4
                                                                                                                                    D
                                                                                                                                    U
                                                                                                                                    pattern
                                                                                                                                    Rdn)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__585 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             20)) == (0x04F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             15
                                                                                                                                             10)) == (0b111100#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__584 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__584 <b 1329) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__585 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1329
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let sf :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          20
                                                                                                                                          1)
                                                                                                                                      let imm4 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
                                                                                                                                      let D :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          11
                                                                                                                                          1)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          1)
                                                                                                                                      let pattern :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let Rdn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      (decode_SQINCD_R_RS_X
                                                                                                                                        size
                                                                                                                                        sf
                                                                                                                                        imm4
                                                                                                                                        D
                                                                                                                                        U
                                                                                                                                        pattern
                                                                                                                                        Rdn)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__587 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 20)) == (0x042#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 10)) == (0b111111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__586 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__586 <b 1330) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__587 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1330
                                                                                                                                          let size :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let sf :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              20
                                                                                                                                              1)
                                                                                                                                          let imm4 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let D :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              11
                                                                                                                                              1)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              10
                                                                                                                                              1)
                                                                                                                                          let pattern :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let Rdn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_UQDECB_R_RS_UW
                                                                                                                                            size
                                                                                                                                            sf
                                                                                                                                            imm4
                                                                                                                                            D
                                                                                                                                            U
                                                                                                                                            pattern
                                                                                                                                            Rdn)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__589 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     20)) == (0x046#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     10)) == (0b111111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__588 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__588 <b 1331) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__589 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1331
                                                                                                                                              let size :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
                                                                                                                                              let sf :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  20
                                                                                                                                                  1)
                                                                                                                                              let imm4 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  4)
                                                                                                                                              let D :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  11
                                                                                                                                                  1)
                                                                                                                                              let U :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  10
                                                                                                                                                  1)
                                                                                                                                              let pattern :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let Rdn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              (decode_UQDECH_R_RS_UW
                                                                                                                                                size
                                                                                                                                                sf
                                                                                                                                                imm4
                                                                                                                                                D
                                                                                                                                                U
                                                                                                                                                pattern
                                                                                                                                                Rdn)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__591 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         20)) == (0x04A#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         15
                                                                                                                                                         10)) == (0b111111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__590 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__590 <b 1332) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__591 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1332
                                                                                                                                                  let size :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      2)
                                                                                                                                                  let sf :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      20
                                                                                                                                                      1)
                                                                                                                                                  let imm4 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      4)
                                                                                                                                                  let D :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      11
                                                                                                                                                      1)
                                                                                                                                                  let U :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      10
                                                                                                                                                      1)
                                                                                                                                                  let pattern :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let Rdn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_UQDECW_R_RS_UW
                                                                                                                                                    size
                                                                                                                                                    sf
                                                                                                                                                    imm4
                                                                                                                                                    D
                                                                                                                                                    U
                                                                                                                                                    pattern
                                                                                                                                                    Rdn)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__593 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             20)) == (0x04E#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             10)) == (0b111111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__592 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__592 <b 1333) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__593 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1333
                                                                                                                                                      let size :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          2)
                                                                                                                                                      let sf :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          20
                                                                                                                                                          1)
                                                                                                                                                      let imm4 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          4)
                                                                                                                                                      let D :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          11
                                                                                                                                                          1)
                                                                                                                                                      let U :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          10
                                                                                                                                                          1)
                                                                                                                                                      let pattern :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let Rdn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_UQDECD_R_RS_UW
                                                                                                                                                        size
                                                                                                                                                        sf
                                                                                                                                                        imm4
                                                                                                                                                        D
                                                                                                                                                        U
                                                                                                                                                        pattern
                                                                                                                                                        Rdn)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__595 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 20)) == (0x042#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 15
                                                                                                                                                                 10)) == (0b111110#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__594 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__594 <b 1334) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__595 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1334
                                                                                                                                                          let size :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              2)
                                                                                                                                                          let sf :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              20
                                                                                                                                                              1)
                                                                                                                                                          let imm4 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              4)
                                                                                                                                                          let D :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              11
                                                                                                                                                              1)
                                                                                                                                                          let U :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              1)
                                                                                                                                                          let pattern :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              5)
                                                                                                                                                          let Rdn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          (decode_SQDECB_R_RS_SX
                                                                                                                                                            size
                                                                                                                                                            sf
                                                                                                                                                            imm4
                                                                                                                                                            D
                                                                                                                                                            U
                                                                                                                                                            pattern
                                                                                                                                                            Rdn)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__597 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     20)) == (0x046#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     15
                                                                                                                                                                     10)) == (0b111110#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__596 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__596 <b 1335) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__597 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 1335
                                                                                                                                                              let size :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  22
                                                                                                                                                                  2)
                                                                                                                                                              let sf :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  20
                                                                                                                                                                  1)
                                                                                                                                                              let imm4 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  4)
                                                                                                                                                              let D :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  11
                                                                                                                                                                  1)
                                                                                                                                                              let U :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  10
                                                                                                                                                                  1)
                                                                                                                                                              let pattern :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  5)
                                                                                                                                                              let Rdn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  5)
                                                                                                                                                              (decode_SQDECH_R_RS_SX
                                                                                                                                                                size
                                                                                                                                                                sf
                                                                                                                                                                imm4
                                                                                                                                                                D
                                                                                                                                                                U
                                                                                                                                                                pattern
                                                                                                                                                                Rdn)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__599 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         20)) == (0x04A#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         15
                                                                                                                                                                         10)) == (0b111110#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__598 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__598 <b 1336) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__599 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 1336
                                                                                                                                                                  let size :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      2)
                                                                                                                                                                  let sf :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      20
                                                                                                                                                                      1)
                                                                                                                                                                  let imm4 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      4)
                                                                                                                                                                  let D :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      11
                                                                                                                                                                      1)
                                                                                                                                                                  let U :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      10
                                                                                                                                                                      1)
                                                                                                                                                                  let pattern :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      5
                                                                                                                                                                      5)
                                                                                                                                                                  let Rdn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      5)
                                                                                                                                                                  (decode_SQDECW_R_RS_SX
                                                                                                                                                                    size
                                                                                                                                                                    sf
                                                                                                                                                                    imm4
                                                                                                                                                                    D
                                                                                                                                                                    U
                                                                                                                                                                    pattern
                                                                                                                                                                    Rdn)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
