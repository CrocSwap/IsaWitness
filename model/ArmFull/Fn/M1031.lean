import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0938
import ArmFull.Fn.M0939
import ArmFull.Fn.M0940
import ArmFull.Fn.M0941

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
def __DecodeA64_SVE__seg4 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__375 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 15 10)) == (0b000000#6 : (BitVec 6))))) : Bool) : Bool)
    then
      (do
        let w__374 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__374 <b 1224) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__375 : Bool)
  then
    (do
      writeReg SEE 1224
      let size := (BitVec.slice __opcode 22 2)
      let Zm := (BitVec.slice __opcode 16 5)
      let Zn := (BitVec.slice __opcode 5 5)
      let Zd := (BitVec.slice __opcode 0 5)
      (decode_ADD_Z_ZZ__ size Zm Zn Zd)
      (pure false))
  else
    (do
      let w__377 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00000100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                 __opcode 15 10)) == (0b001100#6 : (BitVec 6)))) : Bool) : Bool)
        then
          (do
            let w__376 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__376 <b 1225) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__377 : Bool)
      then
        (do
          writeReg SEE 1225
          let Zm := (BitVec.slice __opcode 16 5)
          let Zn := (BitVec.slice __opcode 5 5)
          let Zd := (BitVec.slice __opcode 0 5)
          (decode_AND_Z_ZZ__ Zm Zn Zd)
          (pure false))
      else
        (do
          let w__379 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                     __opcode 15 10)) == (0b001100#6 : (BitVec 6)))) : Bool) : Bool)
            then
              (do
                let w__378 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__378 <b 1226) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__379 : Bool)
          then
            (do
              writeReg SEE 1226
              let Zm := (BitVec.slice __opcode 16 5)
              let Zn := (BitVec.slice __opcode 5 5)
              let Zd := (BitVec.slice __opcode 0 5)
              (decode_BIC_Z_ZZ__ Zm Zn Zd)
              (pure false))
          else
            (do
              let w__381 ← (( do
                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                         __opcode 15 10)) == (0b001100#6 : (BitVec 6)))) : Bool) : Bool)
                then
                  (do
                    let w__380 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__380 <b 1227) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__381 : Bool)
              then
                (do
                  writeReg SEE 1227
                  let Zm := (BitVec.slice __opcode 16 5)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let Zd := (BitVec.slice __opcode 0 5)
                  (decode_EOR_Z_ZZ__ Zm Zn Zd)
                  (pure false))
              else
                (do
                  let w__383 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00000100011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                             __opcode 15 10)) == (0b001100#6 : (BitVec 6)))) : Bool) : Bool)
                    then
                      (do
                        let w__382 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__382 <b 1228) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__383 : Bool)
                  then
                    (do
                      writeReg SEE 1228
                      let Zm := (BitVec.slice __opcode 16 5)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let Zd := (BitVec.slice __opcode 0 5)
                      (decode_ORR_Z_ZZ__ Zm Zn Zd)
                      (pure false))
                  else
                    (do
                      let w__385 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                   __opcode 15 10)) == (0b000001#6 : (BitVec 6))))) : Bool) : Bool)
                        then
                          (do
                            let w__384 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__384 <b 1229) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__385 : Bool)
                      then
                        (do
                          writeReg SEE 1229
                          let size := (BitVec.slice __opcode 22 2)
                          let Zm := (BitVec.slice __opcode 16 5)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let Zd := (BitVec.slice __opcode 0 5)
                          (decode_SUB_Z_ZZ__ size Zm Zn Zd)
                          (pure false))
                      else
                        (do
                          let w__387 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                     __opcode 21 13)) == (0b000000000#9 : (BitVec 9)))) : Bool) : Bool)
                            then
                              (do
                                let w__386 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__386 <b 1230) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__387 : Bool)
                          then
                            (do
                              writeReg SEE 1230
                              let size := (BitVec.slice __opcode 22 2)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Zm := (BitVec.slice __opcode 5 5)
                              let Zdn := (BitVec.slice __opcode 0 5)
                              (decode_ADD_Z_P_ZZ__ size Pg Zm Zdn)
                              (pure false))
                          else
                            (do
                              let w__389 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 21 13)) == (0b011010000#9 : (BitVec 9)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__388 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__388 <b 1231) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__389 : Bool)
                              then
                                (do
                                  writeReg SEE 1231
                                  let size := (BitVec.slice __opcode 22 2)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Zm := (BitVec.slice __opcode 5 5)
                                  let Zdn := (BitVec.slice __opcode 0 5)
                                  (decode_AND_Z_P_ZZ__ size Pg Zm Zdn)
                                  (pure false))
                              else
                                (do
                                  let w__391 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 21 13)) == (0b011011000#9 : (BitVec 9)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__390 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__390 <b 1232) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__391 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1232
                                      let size := (BitVec.slice __opcode 22 2)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Zm := (BitVec.slice __opcode 5 5)
                                      let Zdn := (BitVec.slice __opcode 0 5)
                                      (decode_BIC_Z_P_ZZ__ size Pg Zm Zdn)
                                      (pure false))
                                  else
                                    (do
                                      let w__393 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 21 13)) == (0b011001000#9 : (BitVec 9)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__392 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__392 <b 1233) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__393 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1233
                                          let size := (BitVec.slice __opcode 22 2)
                                          let Pg := (BitVec.slice __opcode 10 3)
                                          let Zm := (BitVec.slice __opcode 5 5)
                                          let Zdn := (BitVec.slice __opcode 0 5)
                                          (decode_EOR_Z_P_ZZ__ size Pg Zm Zdn)
                                          (pure false))
                                      else
                                        (do
                                          let w__395 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 21 13)) == (0b010011100#9 : (BitVec 9)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__394 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__394 <b 1234) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__395 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1234
                                              let size := (BitVec.slice __opcode 22 2)
                                              let R := (BitVec.slice __opcode 18 1)
                                              let L := (BitVec.slice __opcode 17 1)
                                              let U := (BitVec.slice __opcode 16 1)
                                              let Pg := (BitVec.slice __opcode 10 3)
                                              let Zm := (BitVec.slice __opcode 5 5)
                                              let Zdn := (BitVec.slice __opcode 0 5)
                                              (decode_LSL_Z_P_ZZ__ size R L U Pg Zm Zdn)
                                              (pure false))
                                          else
                                            (do
                                              let w__397 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 21 13)) == (0b010111100#9 : (BitVec 9)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__396 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__396 <b 1235) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__397 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1235
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let R := (BitVec.slice __opcode 18 1)
                                                  let L := (BitVec.slice __opcode 17 1)
                                                  let U := (BitVec.slice __opcode 16 1)
                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                  let Zm := (BitVec.slice __opcode 5 5)
                                                  let Zdn := (BitVec.slice __opcode 0 5)
                                                  (decode_LSLR_Z_P_ZZ__ size R L U Pg Zm Zdn)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__399 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 21 13)) == (0b010000000#9 : (BitVec 9)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__398 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__398 <b 1236) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__399 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1236
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let H := (BitVec.slice __opcode 17 1)
                                                      let U := (BitVec.slice __opcode 16 1)
                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                      let Zm := (BitVec.slice __opcode 5 5)
                                                      let Zdn := (BitVec.slice __opcode 0 5)
                                                      (decode_MUL_Z_P_ZZ__ size H U Pg Zm Zdn)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__401 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 21 13)) == (0b011000000#9 : (BitVec 9)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__400 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__400 <b 1237) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__401 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1237
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                          let Zm := (BitVec.slice __opcode 5 5)
                                                          let Zdn := (BitVec.slice __opcode 0 5)
                                                          (decode_ORR_Z_P_ZZ__ size Pg Zm Zdn)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__403 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 21 13)) == (0b000001000#9 : (BitVec 9)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__402 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__402 <b 1238) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__403 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1238
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let Zm := (BitVec.slice __opcode 5 5)
                                                              let Zdn := (BitVec.slice __opcode 0 5)
                                                              (decode_SUB_Z_P_ZZ__ size Pg Zm Zdn)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__405 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 21 13)) == (0b000011000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__404 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__404 <b 1239) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__405 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1239
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zdn :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_SUBR_Z_P_ZZ__ size Pg Zm
                                                                    Zdn)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__407 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 21 13)) == (0b010001100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__406 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__406 <b 1240) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__407 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1240
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let R :=
                                                                        (BitVec.slice __opcode 18 1)
                                                                      let L :=
                                                                        (BitVec.slice __opcode 17 1)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 16 1)
                                                                      let Pg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zdn :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_LSR_Z_P_ZZ__ size R L
                                                                        U Pg Zm Zdn)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__409 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 21 13)) == (0b010000100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__408 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__408 <b 1241) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__409 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1241
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let R :=
                                                                            (BitVec.slice __opcode
                                                                              18 1)
                                                                          let L :=
                                                                            (BitVec.slice __opcode
                                                                              17 1)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              16 1)
                                                                          let Pg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zdn :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_ASR_Z_P_ZZ__ size
                                                                            R L U Pg Zm Zdn)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__411 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 21 13)) == (0b010101100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__410 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__410 <b 1242) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__411 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1242
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let R :=
                                                                                (BitVec.slice
                                                                                  __opcode 18 1)
                                                                              let L :=
                                                                                (BitVec.slice
                                                                                  __opcode 17 1)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 1)
                                                                              let Pg :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Zdn :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_LSRR_Z_P_ZZ__
                                                                                size R L U Pg Zm Zdn)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__413 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 21
                                                                                         13)) == (0b010100100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__412 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__412 <b 1243) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__413 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1243
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let R :=
                                                                                    (BitVec.slice
                                                                                      __opcode 18 1)
                                                                                  let L :=
                                                                                    (BitVec.slice
                                                                                      __opcode 17 1)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 1)
                                                                                  let Pg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Zdn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_ASRR_Z_P_ZZ__
                                                                                    size R L U Pg Zm
                                                                                    Zdn)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__415 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             21 13)) == (0b001101000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__414 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__414 <b 1244) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__415 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1244
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 1)
                                                                                      let Pg :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Zdn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_UABD_Z_P_ZZ__
                                                                                        size U Pg Zm
                                                                                        Zdn)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__417 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 21
                                                                                                 13)) == (0b001100000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__416 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__416 <b 1245) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__417 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1245
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 1)
                                                                                          let Pg :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 3)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Zdn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_SABD_Z_P_ZZ__
                                                                                            size U
                                                                                            Pg Zm
                                                                                            Zdn)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__419 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     21
                                                                                                     13)) == (0b010101000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__418 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__418 <b 1246) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__419 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1246
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let R :=
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
                                                                                              (decode_UDIV_Z_P_ZZ__
                                                                                                size
                                                                                                R U
                                                                                                Pg
                                                                                                Zm
                                                                                                Zdn)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__421 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         21
                                                                                                         13)) == (0b010100000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__420 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__420 <b 1247) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__421 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1247
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      2)
                                                                                                  let R :=
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
                                                                                                  (decode_SDIV_Z_P_ZZ__
                                                                                                    size
                                                                                                    R
                                                                                                    U
                                                                                                    Pg
                                                                                                    Zm
                                                                                                    Zdn)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__423 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             21
                                                                                                             13)) == (0b010111000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__422 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__422 <b 1248) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__423 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1248
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          2)
                                                                                                      let R :=
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
                                                                                                      (decode_UDIVR_Z_P_ZZ__
                                                                                                        size
                                                                                                        R
                                                                                                        U
                                                                                                        Pg
                                                                                                        Zm
                                                                                                        Zdn)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__425 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 21
                                                                                                                 13)) == (0b010110000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__424 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__424 <b 1249) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__425 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1249
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              2)
                                                                                                          let R :=
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
                                                                                                          (decode_SDIVR_Z_P_ZZ__
                                                                                                            size
                                                                                                            R
                                                                                                            U
                                                                                                            Pg
                                                                                                            Zm
                                                                                                            Zdn)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__427 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     21
                                                                                                                     13)) == (0b001001000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__426 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__426 <b 1250) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__427 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1250
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
                                                                                                              (decode_UMAX_Z_P_ZZ__
                                                                                                                size
                                                                                                                U
                                                                                                                Pg
                                                                                                                Zm
                                                                                                                Zdn)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__429 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         21
                                                                                                                         13)) == (0b001000000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__428 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__428 <b 1251) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__429 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1251
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
                                                                                                                  (decode_SMAX_Z_P_ZZ__
                                                                                                                    size
                                                                                                                    U
                                                                                                                    Pg
                                                                                                                    Zm
                                                                                                                    Zdn)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__431 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             21
                                                                                                                             13)) == (0b001011000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__430 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__430 <b 1252) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__431 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1252
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
                                                                                                                      (decode_UMIN_Z_P_ZZ__
                                                                                                                        size
                                                                                                                        U
                                                                                                                        Pg
                                                                                                                        Zm
                                                                                                                        Zdn)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__433 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 21
                                                                                                                                 13)) == (0b001010000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__432 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__432 <b 1253) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__433 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1253
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
                                                                                                                          (decode_SMIN_Z_P_ZZ__
                                                                                                                            size
                                                                                                                            U
                                                                                                                            Pg
                                                                                                                            Zm
                                                                                                                            Zdn)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__435 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     21
                                                                                                                                     13)) == (0b010011000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__434 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__434 <b 1254) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__435 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1254
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let H :=
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
                                                                                                                              (decode_UMULH_Z_P_ZZ__
                                                                                                                                size
                                                                                                                                H
                                                                                                                                U
                                                                                                                                Pg
                                                                                                                                Zm
                                                                                                                                Zdn)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__437 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         21
                                                                                                                                         13)) == (0b010010000#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__436 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__436 <b 1255) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__437 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1255
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let H :=
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
                                                                                                                                  (decode_SMULH_Z_P_ZZ__
                                                                                                                                    size
                                                                                                                                    H
                                                                                                                                    U
                                                                                                                                    Pg
                                                                                                                                    Zm
                                                                                                                                    Zdn)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__439 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 13)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   11
                                                                                                                                                   10)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   4
                                                                                                                                                   4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__438 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__438 <b 1256) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__439 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1256
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
                                                                                                                                      let sf :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          12
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
                                                                                                                                          4
                                                                                                                                          1)
                                                                                                                                      let Pd :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          4)
                                                                                                                                      (decode_WHILELO_P_P_RR__
                                                                                                                                        size
                                                                                                                                        Rm
                                                                                                                                        sf
                                                                                                                                        U
                                                                                                                                        lt
                                                                                                                                        Rn
                                                                                                                                        eq
                                                                                                                                        Pd)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__441 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     13)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       11
                                                                                                                                                       10)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       4
                                                                                                                                                       4)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__440 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__440 <b 1257) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__441 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1257
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
                                                                                                                                          let sf :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              12
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
                                                                                                                                              4
                                                                                                                                              1)
                                                                                                                                          let Pd :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              4)
                                                                                                                                          (decode_WHILELS_P_P_RR__
                                                                                                                                            size
                                                                                                                                            Rm
                                                                                                                                            sf
                                                                                                                                            U
                                                                                                                                            lt
                                                                                                                                            Rn
                                                                                                                                            eq
                                                                                                                                            Pd)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__443 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       21
                                                                                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         15
                                                                                                                                                         13)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           11
                                                                                                                                                           10)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           4
                                                                                                                                                           4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__442 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__442 <b 1258) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__443 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1258
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
                                                                                                                                              let sf :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  12
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
                                                                                                                                                  4
                                                                                                                                                  1)
                                                                                                                                              let Pd :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  4)
                                                                                                                                              (decode_WHILELT_P_P_RR__
                                                                                                                                                size
                                                                                                                                                Rm
                                                                                                                                                sf
                                                                                                                                                U
                                                                                                                                                lt
                                                                                                                                                Rn
                                                                                                                                                eq
                                                                                                                                                Pd)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__445 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           21
                                                                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             13)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               11
                                                                                                                                                               10)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               4
                                                                                                                                                               4)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__444 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__444 <b 1259) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__445 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1259
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
                                                                                                                                                  let sf :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      12
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
                                                                                                                                                      4
                                                                                                                                                      1)
                                                                                                                                                  let Pd :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      4)
                                                                                                                                                  (decode_WHILELE_P_P_RR__
                                                                                                                                                    size
                                                                                                                                                    Rm
                                                                                                                                                    sf
                                                                                                                                                    U
                                                                                                                                                    lt
                                                                                                                                                    Rn
                                                                                                                                                    eq
                                                                                                                                                    Pd)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__447 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               21
                                                                                                                                                               21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 15
                                                                                                                                                                 13)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   11
                                                                                                                                                                   10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   4
                                                                                                                                                                   4)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__446 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__446 <b 1260) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__447 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1260
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
                                                                                                                                                      let sf :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          12
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
                                                                                                                                                          4
                                                                                                                                                          1)
                                                                                                                                                      let Pd :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          4)
                                                                                                                                                      (decode_WHILEHI_P_P_RR__
                                                                                                                                                        size
                                                                                                                                                        Rm
                                                                                                                                                        sf
                                                                                                                                                        U
                                                                                                                                                        lt
                                                                                                                                                        Rn
                                                                                                                                                        eq
                                                                                                                                                        Pd)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__449 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   21
                                                                                                                                                                   21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     15
                                                                                                                                                                     13)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       11
                                                                                                                                                                       10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       4
                                                                                                                                                                       4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__448 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__448 <b 1261) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__449 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1261
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
                                                                                                                                                          let sf :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              12
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
                                                                                                                                                              4
                                                                                                                                                              1)
                                                                                                                                                          let Pd :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              4)
                                                                                                                                                          (decode_WHILEHS_P_P_RR__
                                                                                                                                                            size
                                                                                                                                                            Rm
                                                                                                                                                            sf
                                                                                                                                                            U
                                                                                                                                                            lt
                                                                                                                                                            Rn
                                                                                                                                                            eq
                                                                                                                                                            Pd)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__451 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       21
                                                                                                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         15
                                                                                                                                                                         13)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           11
                                                                                                                                                                           10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           4
                                                                                                                                                                           4)) == (1#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__450 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__450 <b 1262) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__451 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 1262
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
                                                                                                                                                              let sf :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  12
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
                                                                                                                                                                  4
                                                                                                                                                                  1)
                                                                                                                                                              let Pd :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  4)
                                                                                                                                                              (decode_WHILEGT_P_P_RR__
                                                                                                                                                                size
                                                                                                                                                                Rm
                                                                                                                                                                sf
                                                                                                                                                                U
                                                                                                                                                                lt
                                                                                                                                                                Rn
                                                                                                                                                                eq
                                                                                                                                                                Pd)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__453 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           21
                                                                                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             15
                                                                                                                                                                             13)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               11
                                                                                                                                                                               10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               4
                                                                                                                                                                               4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__452 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__452 <b 1263) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__453 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 1263
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
                                                                                                                                                                  let sf :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      12
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
                                                                                                                                                                      4
                                                                                                                                                                      1)
                                                                                                                                                                  let Pd :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      4)
                                                                                                                                                                  (decode_WHILEGE_P_P_RR__
                                                                                                                                                                    size
                                                                                                                                                                    Rm
                                                                                                                                                                    sf
                                                                                                                                                                    U
                                                                                                                                                                    lt
                                                                                                                                                                    Rn
                                                                                                                                                                    eq
                                                                                                                                                                    Pd)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
