import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0946
import ArmFull.Fn.M0947
import ArmFull.Fn.M0948

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
def __DecodeA64_SVE__seg7 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__601 ← (( do
    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0x04E#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
             __opcode 15 10)) == (0b111110#6 : (BitVec 6)))) : Bool) : Bool)
    then
      (do
        let w__600 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__600 <b 1337) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__601 : Bool)
  then
    (do
      writeReg SEE 1337
      let size := (BitVec.slice __opcode 22 2)
      let sf := (BitVec.slice __opcode 20 1)
      let imm4 := (BitVec.slice __opcode 16 4)
      let D := (BitVec.slice __opcode 11 1)
      let U := (BitVec.slice __opcode 10 1)
      let pattern := (BitVec.slice __opcode 5 5)
      let Rdn := (BitVec.slice __opcode 0 5)
      (decode_SQDECD_R_RS_SX size sf imm4 D U pattern Rdn)
      (pure false))
  else
    (do
      let w__603 ← (( do
        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0x043#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                 __opcode 15 10)) == (0b111111#6 : (BitVec 6)))) : Bool) : Bool)
        then
          (do
            let w__602 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__602 <b 1338) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__603 : Bool)
      then
        (do
          writeReg SEE 1338
          let size := (BitVec.slice __opcode 22 2)
          let sf := (BitVec.slice __opcode 20 1)
          let imm4 := (BitVec.slice __opcode 16 4)
          let D := (BitVec.slice __opcode 11 1)
          let U := (BitVec.slice __opcode 10 1)
          let pattern := (BitVec.slice __opcode 5 5)
          let Rdn := (BitVec.slice __opcode 0 5)
          (decode_UQDECB_R_RS_X size sf imm4 D U pattern Rdn)
          (pure false))
      else
        (do
          let w__605 ← (( do
            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0x047#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                     __opcode 15 10)) == (0b111111#6 : (BitVec 6)))) : Bool) : Bool)
            then
              (do
                let w__604 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__604 <b 1339) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__605 : Bool)
          then
            (do
              writeReg SEE 1339
              let size := (BitVec.slice __opcode 22 2)
              let sf := (BitVec.slice __opcode 20 1)
              let imm4 := (BitVec.slice __opcode 16 4)
              let D := (BitVec.slice __opcode 11 1)
              let U := (BitVec.slice __opcode 10 1)
              let pattern := (BitVec.slice __opcode 5 5)
              let Rdn := (BitVec.slice __opcode 0 5)
              (decode_UQDECH_R_RS_X size sf imm4 D U pattern Rdn)
              (pure false))
          else
            (do
              let w__607 ← (( do
                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0x04B#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                         __opcode 15 10)) == (0b111111#6 : (BitVec 6)))) : Bool) : Bool)
                then
                  (do
                    let w__606 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__606 <b 1340) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__607 : Bool)
              then
                (do
                  writeReg SEE 1340
                  let size := (BitVec.slice __opcode 22 2)
                  let sf := (BitVec.slice __opcode 20 1)
                  let imm4 := (BitVec.slice __opcode 16 4)
                  let D := (BitVec.slice __opcode 11 1)
                  let U := (BitVec.slice __opcode 10 1)
                  let pattern := (BitVec.slice __opcode 5 5)
                  let Rdn := (BitVec.slice __opcode 0 5)
                  (decode_UQDECW_R_RS_X size sf imm4 D U pattern Rdn)
                  (pure false))
              else
                (do
                  let w__609 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0x04F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                             __opcode 15 10)) == (0b111111#6 : (BitVec 6)))) : Bool) : Bool)
                    then
                      (do
                        let w__608 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__608 <b 1341) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__609 : Bool)
                  then
                    (do
                      writeReg SEE 1341
                      let size := (BitVec.slice __opcode 22 2)
                      let sf := (BitVec.slice __opcode 20 1)
                      let imm4 := (BitVec.slice __opcode 16 4)
                      let D := (BitVec.slice __opcode 11 1)
                      let U := (BitVec.slice __opcode 10 1)
                      let pattern := (BitVec.slice __opcode 5 5)
                      let Rdn := (BitVec.slice __opcode 0 5)
                      (decode_UQDECD_R_RS_X size sf imm4 D U pattern Rdn)
                      (pure false))
                  else
                    (do
                      let w__611 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31
                                 20)) == (0x043#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                 __opcode 15 10)) == (0b111110#6 : (BitVec 6)))) : Bool) : Bool)
                        then
                          (do
                            let w__610 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__610 <b 1342) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__611 : Bool)
                      then
                        (do
                          writeReg SEE 1342
                          let size := (BitVec.slice __opcode 22 2)
                          let sf := (BitVec.slice __opcode 20 1)
                          let imm4 := (BitVec.slice __opcode 16 4)
                          let D := (BitVec.slice __opcode 11 1)
                          let U := (BitVec.slice __opcode 10 1)
                          let pattern := (BitVec.slice __opcode 5 5)
                          let Rdn := (BitVec.slice __opcode 0 5)
                          (decode_SQDECB_R_RS_X size sf imm4 D U pattern Rdn)
                          (pure false))
                      else
                        (do
                          let w__613 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0x047#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                     __opcode 15 10)) == (0b111110#6 : (BitVec 6)))) : Bool) : Bool)
                            then
                              (do
                                let w__612 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__612 <b 1343) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__613 : Bool)
                          then
                            (do
                              writeReg SEE 1343
                              let size := (BitVec.slice __opcode 22 2)
                              let sf := (BitVec.slice __opcode 20 1)
                              let imm4 := (BitVec.slice __opcode 16 4)
                              let D := (BitVec.slice __opcode 11 1)
                              let U := (BitVec.slice __opcode 10 1)
                              let pattern := (BitVec.slice __opcode 5 5)
                              let Rdn := (BitVec.slice __opcode 0 5)
                              (decode_SQDECH_R_RS_X size sf imm4 D U pattern Rdn)
                              (pure false))
                          else
                            (do
                              let w__615 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                         __opcode 31 20)) == (0x04B#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                         __opcode 15 10)) == (0b111110#6 : (BitVec 6)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__614 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__614 <b 1344) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__615 : Bool)
                              then
                                (do
                                  writeReg SEE 1344
                                  let size := (BitVec.slice __opcode 22 2)
                                  let sf := (BitVec.slice __opcode 20 1)
                                  let imm4 := (BitVec.slice __opcode 16 4)
                                  let D := (BitVec.slice __opcode 11 1)
                                  let U := (BitVec.slice __opcode 10 1)
                                  let pattern := (BitVec.slice __opcode 5 5)
                                  let Rdn := (BitVec.slice __opcode 0 5)
                                  (decode_SQDECW_R_RS_X size sf imm4 D U pattern Rdn)
                                  (pure false))
                              else
                                (do
                                  let w__617 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 31 20)) == (0x04F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                             __opcode 15 10)) == (0b111110#6 : (BitVec 6)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__616 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__616 <b 1345) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__617 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1345
                                      let size := (BitVec.slice __opcode 22 2)
                                      let sf := (BitVec.slice __opcode 20 1)
                                      let imm4 := (BitVec.slice __opcode 16 4)
                                      let D := (BitVec.slice __opcode 11 1)
                                      let U := (BitVec.slice __opcode 10 1)
                                      let pattern := (BitVec.slice __opcode 5 5)
                                      let Rdn := (BitVec.slice __opcode 0 5)
                                      (decode_SQDECD_R_RS_X size sf imm4 D U pattern Rdn)
                                      (pure false))
                                  else
                                    (do
                                      let w__619 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 31 20)) == (0x042#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                 __opcode 15 10)) == (0b111000#6 : (BitVec 6)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__618 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__618 <b 1346) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__619 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1346
                                          let size := (BitVec.slice __opcode 22 2)
                                          let imm4 := (BitVec.slice __opcode 16 4)
                                          let pattern := (BitVec.slice __opcode 5 5)
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          (decode_CNTB_R_S__ size imm4 pattern Rd)
                                          (pure false))
                                      else
                                        (do
                                          let w__621 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 31 20)) == (0x046#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                     __opcode 15 10)) == (0b111000#6 : (BitVec 6)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__620 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__620 <b 1347) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__621 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1347
                                              let size := (BitVec.slice __opcode 22 2)
                                              let imm4 := (BitVec.slice __opcode 16 4)
                                              let pattern := (BitVec.slice __opcode 5 5)
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              (decode_CNTH_R_S__ size imm4 pattern Rd)
                                              (pure false))
                                          else
                                            (do
                                              let w__623 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 31 20)) == (0x04A#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                         __opcode 15 10)) == (0b111000#6 : (BitVec 6)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__622 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__622 <b 1348) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__623 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1348
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let imm4 := (BitVec.slice __opcode 16 4)
                                                  let pattern := (BitVec.slice __opcode 5 5)
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  (decode_CNTW_R_S__ size imm4 pattern Rd)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__625 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 31 20)) == (0x04E#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                             __opcode 15 10)) == (0b111000#6 : (BitVec 6)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__624 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__624 <b 1349) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__625 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1349
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let imm4 := (BitVec.slice __opcode 16 4)
                                                      let pattern := (BitVec.slice __opcode 5 5)
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      (decode_CNTD_R_S__ size imm4 pattern Rd)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__627 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0x047#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                 __opcode 15 10)) == (0b110001#6 : (BitVec 6)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__626 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__626 <b 1350) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__627 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1350
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let imm4 := (BitVec.slice __opcode 16 4)
                                                          let D := (BitVec.slice __opcode 10 1)
                                                          let pattern := (BitVec.slice __opcode 5 5)
                                                          let Zdn := (BitVec.slice __opcode 0 5)
                                                          (decode_DECH_Z_ZS__ size imm4 D pattern
                                                            Zdn)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__629 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0x04B#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                     __opcode 15 10)) == (0b110001#6 : (BitVec 6)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__628 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__628 <b 1351) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__629 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1351
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let imm4 :=
                                                                (BitVec.slice __opcode 16 4)
                                                              let D := (BitVec.slice __opcode 10 1)
                                                              let pattern :=
                                                                (BitVec.slice __opcode 5 5)
                                                              let Zdn := (BitVec.slice __opcode 0 5)
                                                              (decode_DECW_Z_ZS__ size imm4 D
                                                                pattern Zdn)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__631 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 31 20)) == (0x04F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                         __opcode 15 10)) == (0b110001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__630 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__630 <b 1352) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__631 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1352
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let imm4 :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let D :=
                                                                    (BitVec.slice __opcode 10 1)
                                                                  let pattern :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zdn :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_DECD_Z_ZS__ size imm4 D
                                                                    pattern Zdn)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__633 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0x047#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                             __opcode 15 10)) == (0b110000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__632 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__632 <b 1353) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__633 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1353
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let imm4 :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let D :=
                                                                        (BitVec.slice __opcode 10 1)
                                                                      let pattern :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zdn :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_INCH_Z_ZS__ size imm4
                                                                        D pattern Zdn)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__635 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 20)) == (0x04B#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 10)) == (0b110000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__634 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__634 <b 1354) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__635 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1354
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let imm4 :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              10 1)
                                                                          let pattern :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zdn :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_INCW_Z_ZS__ size
                                                                            imm4 D pattern Zdn)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__637 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 20)) == (0x04F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 10)) == (0b110000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__636 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__636 <b 1355) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__637 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1355
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let imm4 :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 1)
                                                                              let pattern :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Zdn :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_INCD_Z_ZS__
                                                                                size imm4 D pattern
                                                                                Zdn)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__639 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0x046#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         10)) == (0b110001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__638 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__638 <b 1356) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__639 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1356
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
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
                                                                                  let Zdn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_UQINCH_Z_ZS__
                                                                                    size imm4 D U
                                                                                    pattern Zdn)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__641 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0x04A#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 10)) == (0b110001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__640 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__640 <b 1357) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__641 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1357
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
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
                                                                                      let Zdn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_UQINCW_Z_ZS__
                                                                                        size imm4 D
                                                                                        U pattern
                                                                                        Zdn)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__643 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0x04E#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 10)) == (0b110001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__642 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__642 <b 1358) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__643 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1358
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
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
                                                                                          let Zdn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_UQINCD_Z_ZS__
                                                                                            size
                                                                                            imm4 D U
                                                                                            pattern
                                                                                            Zdn)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__645 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     20)) == (0x046#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     10)) == (0b110000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__644 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__644 <b 1359) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__645 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1359
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
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
                                                                                              let Zdn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              (decode_SQINCH_Z_ZS__
                                                                                                size
                                                                                                imm4
                                                                                                D U
                                                                                                pattern
                                                                                                Zdn)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__647 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         20)) == (0x04A#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         10)) == (0b110000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__646 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__646 <b 1360) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__647 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1360
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      2)
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
                                                                                                  let Zdn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  (decode_SQINCW_Z_ZS__
                                                                                                    size
                                                                                                    imm4
                                                                                                    D
                                                                                                    U
                                                                                                    pattern
                                                                                                    Zdn)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__649 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0x04E#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             10)) == (0b110000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__648 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__648 <b 1361) : Bool))))
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
                                                                                                      writeReg SEE 1361
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          2)
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
                                                                                                      let Zdn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      (decode_SQINCD_Z_ZS__
                                                                                                        size
                                                                                                        imm4
                                                                                                        D
                                                                                                        U
                                                                                                        pattern
                                                                                                        Zdn)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__651 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0x046#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 10)) == (0b110011#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__650 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__650 <b 1362) : Bool))))
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
                                                                                                          writeReg SEE 1362
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              2)
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
                                                                                                          let Zdn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          (decode_UQDECH_Z_ZS__
                                                                                                            size
                                                                                                            imm4
                                                                                                            D
                                                                                                            U
                                                                                                            pattern
                                                                                                            Zdn)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__653 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0x04A#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     10)) == (0b110011#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__652 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__652 <b 1363) : Bool))))
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
                                                                                                              writeReg SEE 1363
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
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
                                                                                                              let Zdn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              (decode_UQDECW_Z_ZS__
                                                                                                                size
                                                                                                                imm4
                                                                                                                D
                                                                                                                U
                                                                                                                pattern
                                                                                                                Zdn)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__655 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0x04E#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         10)) == (0b110011#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__654 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__654 <b 1364) : Bool))))
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
                                                                                                                  writeReg SEE 1364
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
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
                                                                                                                  let Zdn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  (decode_UQDECD_Z_ZS__
                                                                                                                    size
                                                                                                                    imm4
                                                                                                                    D
                                                                                                                    U
                                                                                                                    pattern
                                                                                                                    Zdn)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__657 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0x046#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             10)) == (0b110010#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__656 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__656 <b 1365) : Bool))))
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
                                                                                                                      writeReg SEE 1365
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
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
                                                                                                                      let Zdn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      (decode_SQDECH_Z_ZS__
                                                                                                                        size
                                                                                                                        imm4
                                                                                                                        D
                                                                                                                        U
                                                                                                                        pattern
                                                                                                                        Zdn)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__659 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 20)) == (0x04A#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 15
                                                                                                                                 10)) == (0b110010#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__658 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__658 <b 1366) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__659 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1366
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
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
                                                                                                                          let Zdn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          (decode_SQDECW_Z_ZS__
                                                                                                                            size
                                                                                                                            imm4
                                                                                                                            D
                                                                                                                            U
                                                                                                                            pattern
                                                                                                                            Zdn)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__661 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     20)) == (0x04E#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     15
                                                                                                                                     10)) == (0b110010#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__660 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__660 <b 1367) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__661 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1367
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
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
                                                                                                                              let Zdn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              (decode_SQDECD_Z_ZS__
                                                                                                                                size
                                                                                                                                imm4
                                                                                                                                D
                                                                                                                                U
                                                                                                                                pattern
                                                                                                                                Zdn)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__663 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         23)) == (0b001001011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             15
                                                                                                                                             10)) == (0b001000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             4
                                                                                                                                             0)) == (0b00000#5 : (BitVec 5)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__662 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__662 <b 1368) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__663 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1368
                                                                                                                                  let sz :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      1)
                                                                                                                                  let Rm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let ne :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      4
                                                                                                                                      1)
                                                                                                                                  (decode_CTERMEQ_RR__
                                                                                                                                    sz
                                                                                                                                    Rm
                                                                                                                                    Rn
                                                                                                                                    ne)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__665 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             23)) == (0b001001011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 10)) == (0b001000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 4
                                                                                                                                                 0)) == (0b10000#5 : (BitVec 5)))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__664 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__664 <b 1369) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__665 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1369
                                                                                                                                      let sz :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          1)
                                                                                                                                      let Rm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let ne :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          4
                                                                                                                                          1)
                                                                                                                                      (decode_CTERMNE_RR__
                                                                                                                                        sz
                                                                                                                                        Rm
                                                                                                                                        Rn
                                                                                                                                        ne)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__667 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 21
                                                                                                                                                 13)) == (0b111001110#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__666 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__666 <b 1370) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__667 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1370
                                                                                                                                          let size :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let imm8 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              8)
                                                                                                                                          let Zd :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_FDUP_Z_I__
                                                                                                                                            size
                                                                                                                                            imm8
                                                                                                                                            Zd)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__669 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       21
                                                                                                                                                       20)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       13)) == (0b110#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__668 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__668 <b 1371) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__669 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1371
                                                                                                                                              let size :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
                                                                                                                                              let Pg :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  4)
                                                                                                                                              let imm8 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  8)
                                                                                                                                              let Zd :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              (decode_FCPY_Z_P_I__
                                                                                                                                                size
                                                                                                                                                Pg
                                                                                                                                                imm8
                                                                                                                                                Zd)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__671 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         21
                                                                                                                                                         14)) == (0xE3#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__670 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__670 <b 1372) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__671 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1372
                                                                                                                                                  let size :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      2)
                                                                                                                                                  let sh :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      13
                                                                                                                                                      1)
                                                                                                                                                  let imm8 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      8)
                                                                                                                                                  let Zd :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_DUP_Z_I__
                                                                                                                                                    size
                                                                                                                                                    sh
                                                                                                                                                    imm8
                                                                                                                                                    Zd)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__673 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               21
                                                                                                                                                               20)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               15
                                                                                                                                                               14)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__672 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__672 <b 1373) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__673 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1373
                                                                                                                                                      let size :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          2)
                                                                                                                                                      let Pg :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          4)
                                                                                                                                                      let M :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          14
                                                                                                                                                          1)
                                                                                                                                                      let sh :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          13
                                                                                                                                                          1)
                                                                                                                                                      let imm8 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          8)
                                                                                                                                                      let Zd :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_CPY_Z_P_I__
                                                                                                                                                        size
                                                                                                                                                        Pg
                                                                                                                                                        M
                                                                                                                                                        sh
                                                                                                                                                        imm8
                                                                                                                                                        Zd)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__675 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   21
                                                                                                                                                                   20)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   15
                                                                                                                                                                   14)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__674 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__674 <b 1374) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__675 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1374
                                                                                                                                                          let size :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              2)
                                                                                                                                                          let Pg :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              4)
                                                                                                                                                          let M :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              14
                                                                                                                                                              1)
                                                                                                                                                          let sh :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              13
                                                                                                                                                              1)
                                                                                                                                                          let imm8 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              8)
                                                                                                                                                          let Zd :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          (decode_CPY_Z_O_I__
                                                                                                                                                            size
                                                                                                                                                            Pg
                                                                                                                                                            M
                                                                                                                                                            sh
                                                                                                                                                            imm8
                                                                                                                                                            Zd)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__677 ← (( do
                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   31
                                                                                                                                                                   18)) == (0b00000101110000#14 : (BitVec 14))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__676 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__676 <b 1375) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__677 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 1375
                                                                                                                                                              let imm13 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  13)
                                                                                                                                                              let Zd :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  5)
                                                                                                                                                              (decode_DUPM_Z_I__
                                                                                                                                                                imm13
                                                                                                                                                                Zd)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__679 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         21
                                                                                                                                                                         13)) == (0b010001101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__678 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__678 <b 1376) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__679 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 1376
                                                                                                                                                                  let size :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      2)
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
                                                                                                                                                                  (decode_UXTB_Z_P_Z__
                                                                                                                                                                    size
                                                                                                                                                                    U
                                                                                                                                                                    Pg
                                                                                                                                                                    Zn
                                                                                                                                                                    Zd)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__681 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             21
                                                                                                                                                                             13)) == (0b010011101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__680 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__680 <b 1377) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__681 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 1377
                                                                                                                                                                      let size :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          22
                                                                                                                                                                          2)
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
                                                                                                                                                                      (decode_UXTH_Z_P_Z__
                                                                                                                                                                        size
                                                                                                                                                                        U
                                                                                                                                                                        Pg
                                                                                                                                                                        Zn
                                                                                                                                                                        Zd)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__683 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 21
                                                                                                                                                                                 13)) == (0b010101101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__682 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__682 <b 1378) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__683 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 1378
                                                                                                                                                                          let size :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              22
                                                                                                                                                                              2)
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
                                                                                                                                                                          (decode_UXTW_Z_P_Z__
                                                                                                                                                                            size
                                                                                                                                                                            U
                                                                                                                                                                            Pg
                                                                                                                                                                            Zn
                                                                                                                                                                            Zd)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
