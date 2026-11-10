import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0941
import ArmFull.Fn.M0942
import ArmFull.Fn.M0943
import ArmFull.Fn.M0944

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
def __DecodeA64_SVE__seg5 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__455 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 __opcode 15 13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
    then
      (do
        let w__454 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__454 <b 1264) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__455 : Bool)
  then
    (do
      writeReg SEE 1264
      let size := (BitVec.slice __opcode 22 2)
      let imm5 := (BitVec.slice __opcode 16 5)
      let Pg := (BitVec.slice __opcode 10 3)
      let Zn := (BitVec.slice __opcode 5 5)
      let ne := (BitVec.slice __opcode 4 1)
      let Pd := (BitVec.slice __opcode 0 4)
      (decode_CMPEQ_P_P_ZI__ size imm5 Pg Zn ne Pd)
      (pure false))
  else
    (do
      let w__457 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     __opcode 15 13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
        then
          (do
            let w__456 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__456 <b 1265) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__457 : Bool)
      then
        (do
          writeReg SEE 1265
          let size := (BitVec.slice __opcode 22 2)
          let imm5 := (BitVec.slice __opcode 16 5)
          let Pg := (BitVec.slice __opcode 10 3)
          let Zn := (BitVec.slice __opcode 5 5)
          let ne := (BitVec.slice __opcode 4 1)
          let Pd := (BitVec.slice __opcode 0 4)
          (decode_CMPNE_P_P_ZI__ size imm5 Pg Zn ne Pd)
          (pure false))
      else
        (do
          let w__459 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 13 13)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
            then
              (do
                let w__458 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__458 <b 1266) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__459 : Bool)
          then
            (do
              writeReg SEE 1266
              let size := (BitVec.slice __opcode 22 2)
              let imm7 := (BitVec.slice __opcode 14 7)
              let lt := (BitVec.slice __opcode 13 1)
              let Pg := (BitVec.slice __opcode 10 3)
              let Zn := (BitVec.slice __opcode 5 5)
              let ne := (BitVec.slice __opcode 4 1)
              let Pd := (BitVec.slice __opcode 0 4)
              (decode_CMPHS_P_P_ZI__ size imm7 lt Pg Zn ne Pd)
              (pure false))
          else
            (do
              let w__461 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 13 13)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                then
                  (do
                    let w__460 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__460 <b 1267) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__461 : Bool)
              then
                (do
                  writeReg SEE 1267
                  let size := (BitVec.slice __opcode 22 2)
                  let imm7 := (BitVec.slice __opcode 14 7)
                  let lt := (BitVec.slice __opcode 13 1)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let ne := (BitVec.slice __opcode 4 1)
                  let Pd := (BitVec.slice __opcode 0 4)
                  (decode_CMPHI_P_P_ZI__ size imm7 lt Pg Zn ne Pd)
                  (pure false))
              else
                (do
                  let w__463 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 13 13)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                    then
                      (do
                        let w__462 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__462 <b 1268) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__463 : Bool)
                  then
                    (do
                      writeReg SEE 1268
                      let size := (BitVec.slice __opcode 22 2)
                      let imm7 := (BitVec.slice __opcode 14 7)
                      let lt := (BitVec.slice __opcode 13 1)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let ne := (BitVec.slice __opcode 4 1)
                      let Pd := (BitVec.slice __opcode 0 4)
                      (decode_CMPLO_P_P_ZI__ size imm7 lt Pg Zn ne Pd)
                      (pure false))
                  else
                    (do
                      let w__465 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 13 13)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                        then
                          (do
                            let w__464 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__464 <b 1269) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__465 : Bool)
                      then
                        (do
                          writeReg SEE 1269
                          let size := (BitVec.slice __opcode 22 2)
                          let imm7 := (BitVec.slice __opcode 14 7)
                          let lt := (BitVec.slice __opcode 13 1)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let ne := (BitVec.slice __opcode 4 1)
                          let Pd := (BitVec.slice __opcode 0 4)
                          (decode_CMPLS_P_P_ZI__ size imm7 lt Pg Zn ne Pd)
                          (pure false))
                      else
                        (do
                          let w__467 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                            then
                              (do
                                let w__466 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__466 <b 1270) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__467 : Bool)
                          then
                            (do
                              writeReg SEE 1270
                              let size := (BitVec.slice __opcode 22 2)
                              let imm5 := (BitVec.slice __opcode 16 5)
                              let lt := (BitVec.slice __opcode 13 1)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let ne := (BitVec.slice __opcode 4 1)
                              let Pd := (BitVec.slice __opcode 0 4)
                              (decode_CMPGE_P_P_ZI__ size imm5 lt Pg Zn ne Pd)
                              (pure false))
                          else
                            (do
                              let w__469 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__468 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__468 <b 1271) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__469 : Bool)
                              then
                                (do
                                  writeReg SEE 1271
                                  let size := (BitVec.slice __opcode 22 2)
                                  let imm5 := (BitVec.slice __opcode 16 5)
                                  let lt := (BitVec.slice __opcode 13 1)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Zn := (BitVec.slice __opcode 5 5)
                                  let ne := (BitVec.slice __opcode 4 1)
                                  let Pd := (BitVec.slice __opcode 0 4)
                                  (decode_CMPGT_P_P_ZI__ size imm5 lt Pg Zn ne Pd)
                                  (pure false))
                              else
                                (do
                                  let w__471 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__470 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__470 <b 1272) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__471 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1272
                                      let size := (BitVec.slice __opcode 22 2)
                                      let imm5 := (BitVec.slice __opcode 16 5)
                                      let lt := (BitVec.slice __opcode 13 1)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let ne := (BitVec.slice __opcode 4 1)
                                      let Pd := (BitVec.slice __opcode 0 4)
                                      (decode_CMPLT_P_P_ZI__ size imm5 lt Pg Zn ne Pd)
                                      (pure false))
                                  else
                                    (do
                                      let w__473 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 31 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__472 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__472 <b 1273) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__473 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1273
                                          let size := (BitVec.slice __opcode 22 2)
                                          let imm5 := (BitVec.slice __opcode 16 5)
                                          let lt := (BitVec.slice __opcode 13 1)
                                          let Pg := (BitVec.slice __opcode 10 3)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let ne := (BitVec.slice __opcode 4 1)
                                          let Pd := (BitVec.slice __opcode 0 4)
                                          (decode_CMPLE_P_P_ZI__ size imm5 lt Pg Zn ne Pd)
                                          (pure false))
                                      else
                                        (do
                                          let w__475 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__474 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__474 <b 1274) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__475 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1274
                                              let size := (BitVec.slice __opcode 22 2)
                                              let Zm := (BitVec.slice __opcode 16 5)
                                              let Pg := (BitVec.slice __opcode 10 3)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let ne := (BitVec.slice __opcode 4 1)
                                              let Pd := (BitVec.slice __opcode 0 4)
                                              (decode_CMPEQ_P_P_ZW__ size Zm Pg Zn ne Pd)
                                              (pure false))
                                          else
                                            (do
                                              let w__477 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__476 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__476 <b 1275) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__477 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1275
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let Zm := (BitVec.slice __opcode 16 5)
                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let ne := (BitVec.slice __opcode 4 1)
                                                  let Pd := (BitVec.slice __opcode 0 4)
                                                  (decode_CMPNE_P_P_ZW__ size Zm Pg Zn ne Pd)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__479 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__478 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__478 <b 1276) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__479 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1276
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let Zm := (BitVec.slice __opcode 16 5)
                                                      let U := (BitVec.slice __opcode 15 1)
                                                      let lt := (BitVec.slice __opcode 13 1)
                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let ne := (BitVec.slice __opcode 4 1)
                                                      let Pd := (BitVec.slice __opcode 0 4)
                                                      (decode_CMPHS_P_P_ZW__ size Zm U lt Pg Zn ne
                                                        Pd)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__481 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__480 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__480 <b 1277) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__481 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1277
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let Zm := (BitVec.slice __opcode 16 5)
                                                          let U := (BitVec.slice __opcode 15 1)
                                                          let lt := (BitVec.slice __opcode 13 1)
                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let ne := (BitVec.slice __opcode 4 1)
                                                          let Pd := (BitVec.slice __opcode 0 4)
                                                          (decode_CMPHI_P_P_ZW__ size Zm U lt Pg Zn
                                                            ne Pd)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__483 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                         __opcode 15 13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__482 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__482 <b 1278) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__483 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1278
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let Zm := (BitVec.slice __opcode 16 5)
                                                              let U := (BitVec.slice __opcode 15 1)
                                                              let lt := (BitVec.slice __opcode 13 1)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let ne := (BitVec.slice __opcode 4 1)
                                                              let Pd := (BitVec.slice __opcode 0 4)
                                                              (decode_CMPLO_P_P_ZW__ size Zm U lt Pg
                                                                Zn ne Pd)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__485 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                             __opcode 15 13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__484 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__484 <b 1279) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__485 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1279
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 15 1)
                                                                  let lt :=
                                                                    (BitVec.slice __opcode 13 1)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let ne :=
                                                                    (BitVec.slice __opcode 4 1)
                                                                  let Pd :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_CMPLS_P_P_ZW__ size Zm U
                                                                    lt Pg Zn ne Pd)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__487 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__486 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__486 <b 1280) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__487 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1280
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 15 1)
                                                                      let lt :=
                                                                        (BitVec.slice __opcode 13 1)
                                                                      let Pg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let ne :=
                                                                        (BitVec.slice __opcode 4 1)
                                                                      let Pd :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_CMPGE_P_P_ZW__ size Zm
                                                                        U lt Pg Zn ne Pd)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__489 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__488 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__488 <b 1281) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__489 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1281
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              15 1)
                                                                          let lt :=
                                                                            (BitVec.slice __opcode
                                                                              13 1)
                                                                          let Pg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let ne :=
                                                                            (BitVec.slice __opcode 4
                                                                              1)
                                                                          let Pd :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_CMPGT_P_P_ZW__
                                                                            size Zm U lt Pg Zn ne Pd)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__491 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 4
                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__490 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__490 <b 1282) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__491 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1282
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 15 1)
                                                                              let lt :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 1)
                                                                              let Pg :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let ne :=
                                                                                (BitVec.slice
                                                                                  __opcode 4 1)
                                                                              let Pd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_CMPLT_P_P_ZW__
                                                                                size Zm U lt Pg Zn
                                                                                ne Pd)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__493 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__492 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__492 <b 1283) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__493 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1283
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 15 1)
                                                                                  let lt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 1)
                                                                                  let Pg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let ne :=
                                                                                    (BitVec.slice
                                                                                      __opcode 4 1)
                                                                                  let Pd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_CMPLE_P_P_ZW__
                                                                                    size Zm U lt Pg
                                                                                    Zn ne Pd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__495 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__494 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__494 <b 1284) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__495 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1284
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let Pg :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let ne :=
                                                                                        (BitVec.slice
                                                                                          __opcode 4
                                                                                          1)
                                                                                      let Pd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_CMPEQ_P_P_ZZ__
                                                                                        size Zm Pg
                                                                                        Zn ne Pd)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__497 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     4
                                                                                                     4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__496 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__496 <b 1285) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__497 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1285
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let Pg :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 3)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let ne :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              4 1)
                                                                                          let Pd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_CMPNE_P_P_ZZ__
                                                                                            size Zm
                                                                                            Pg Zn ne
                                                                                            Pd)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__499 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         4
                                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__498 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__498 <b 1286) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__499 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1286
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
                                                                                              let ne :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  4
                                                                                                  1)
                                                                                              let Pd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_CMPGE_P_P_ZZ__
                                                                                                size
                                                                                                Zm
                                                                                                Pg
                                                                                                Zn
                                                                                                ne
                                                                                                Pd)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__501 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             4
                                                                                                             4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__500 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__500 <b 1287) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__501 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1287
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
                                                                                                  let ne :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      4
                                                                                                      1)
                                                                                                  let Pd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_CMPGT_P_P_ZZ__
                                                                                                    size
                                                                                                    Zm
                                                                                                    Pg
                                                                                                    Zn
                                                                                                    ne
                                                                                                    Pd)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__503 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 4
                                                                                                                 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__502 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__502 <b 1288) : Bool))))
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
                                                                                                      writeReg SEE 1288
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
                                                                                                      let ne :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          4
                                                                                                          1)
                                                                                                      let Pd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_CMPHS_P_P_ZZ__
                                                                                                        size
                                                                                                        Zm
                                                                                                        Pg
                                                                                                        Zn
                                                                                                        ne
                                                                                                        Pd)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__505 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 24)) == (0x24#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     4
                                                                                                                     4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__504 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__504 <b 1289) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__505 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1289
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
                                                                                                          let ne :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              4
                                                                                                              1)
                                                                                                          let Pd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_CMPHI_P_P_ZZ__
                                                                                                            size
                                                                                                            Zm
                                                                                                            Pg
                                                                                                            Zn
                                                                                                            ne
                                                                                                            Pd)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__507 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     21
                                                                                                                     9)) == (0b1011011000100#13 : (BitVec 13)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__506 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__506 <b 1290) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__507 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1290
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
                                                                                                              let D :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  1)
                                                                                                              let Pm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  4)
                                                                                                              let Rdn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              (decode_DECP_R_P_R__
                                                                                                                size
                                                                                                                D
                                                                                                                Pm
                                                                                                                Rdn)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__509 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         21
                                                                                                                         9)) == (0b1011001000100#13 : (BitVec 13)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__508 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__508 <b 1291) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__509 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1291
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
                                                                                                                  let D :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      1)
                                                                                                                  let Pm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      4)
                                                                                                                  let Rdn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  (decode_INCP_R_P_R__
                                                                                                                    size
                                                                                                                    D
                                                                                                                    Pm
                                                                                                                    Rdn)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__511 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             21
                                                                                                                             9)) == (0b1010011000100#13 : (BitVec 13)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__510 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__510 <b 1292) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__511 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1292
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let D :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          17
                                                                                                                          1)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          1)
                                                                                                                      let sf :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          1)
                                                                                                                      let Pm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          4)
                                                                                                                      let Rdn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      (decode_UQINCP_R_P_R_UW
                                                                                                                        size
                                                                                                                        D
                                                                                                                        U
                                                                                                                        sf
                                                                                                                        Pm
                                                                                                                        Rdn)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__513 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 21
                                                                                                                                 9)) == (0b1010001000100#13 : (BitVec 13)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__512 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__512 <b 1293) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__513 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1293
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let D :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              17
                                                                                                                              1)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              1)
                                                                                                                          let sf :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              1)
                                                                                                                          let Pm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              4)
                                                                                                                          let Rdn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          (decode_SQINCP_R_P_R_SX
                                                                                                                            size
                                                                                                                            D
                                                                                                                            U
                                                                                                                            sf
                                                                                                                            Pm
                                                                                                                            Rdn)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__515 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     21
                                                                                                                                     9)) == (0b1010011000110#13 : (BitVec 13)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__514 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__514 <b 1294) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__515 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1294
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let D :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  17
                                                                                                                                  1)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  1)
                                                                                                                              let sf :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  1)
                                                                                                                              let Pm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  4)
                                                                                                                              let Rdn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              (decode_UQINCP_R_P_R_X
                                                                                                                                size
                                                                                                                                D
                                                                                                                                U
                                                                                                                                sf
                                                                                                                                Pm
                                                                                                                                Rdn)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__517 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         21
                                                                                                                                         9)) == (0b1010001000110#13 : (BitVec 13)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__516 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__516 <b 1295) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__517 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1295
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let D :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      17
                                                                                                                                      1)
                                                                                                                                  let U :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      1)
                                                                                                                                  let sf :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      1)
                                                                                                                                  let Pm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      4)
                                                                                                                                  let Rdn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  (decode_SQINCP_R_P_R_X
                                                                                                                                    size
                                                                                                                                    D
                                                                                                                                    U
                                                                                                                                    sf
                                                                                                                                    Pm
                                                                                                                                    Rdn)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__519 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             24)) == (0x25#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             21
                                                                                                                                             9)) == (0b1010111000100#13 : (BitVec 13)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__518 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__518 <b 1296) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__519 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1296
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let D :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          17
                                                                                                                                          1)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          1)
                                                                                                                                      let sf :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          1)
                                                                                                                                      let Pm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          4)
                                                                                                                                      let Rdn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      (decode_UQDECP_R_P_R_UW
                                                                                                                                        size
                                                                                                                                        D
                                                                                                                                        U
                                                                                                                                        sf
                                                                                                                                        Pm
                                                                                                                                        Rdn)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))


end ArmFull.Functions
