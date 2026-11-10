import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0951
import ArmFull.Fn.M0952
import ArmFull.Fn.M0953
import ArmFull.Fn.M0954
import ArmFull.Fn.M1024
import ArmFull.Fn.M1025

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
def __DecodeA64_SVE__seg9 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__773 ← (( do
    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00000101101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
             __opcode 15 10)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
    then
      (do
        let w__772 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__772 <b 1423) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__773 : Bool)
  then
    (do
      writeReg SEE 1423
      let Zm := (BitVec.slice __opcode 16 5)
      let H := (BitVec.slice __opcode 10 1)
      let Zn := (BitVec.slice __opcode 5 5)
      let Zd := (BitVec.slice __opcode 0 5)
      (decode_ZIP1_Z_ZZ_Q Zm H Zn Zd)
      (pure false))
  else
    (do
      let w__775 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00000101101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                 __opcode 15 10)) == (0b000001#6 : (BitVec 6)))) : Bool) : Bool)
        then
          (do
            let w__774 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__774 <b 1424) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__775 : Bool)
      then
        (do
          writeReg SEE 1424
          let Zm := (BitVec.slice __opcode 16 5)
          let H := (BitVec.slice __opcode 10 1)
          let Zn := (BitVec.slice __opcode 5 5)
          let Zd := (BitVec.slice __opcode 0 5)
          (decode_ZIP2_Z_ZZ_Q Zm H Zn Zd)
          (pure false))
      else
        (do
          let w__777 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00000101101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                     __opcode 15 10)) == (0b000010#6 : (BitVec 6)))) : Bool) : Bool)
            then
              (do
                let w__776 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__776 <b 1425) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__777 : Bool)
          then
            (do
              writeReg SEE 1425
              let Zm := (BitVec.slice __opcode 16 5)
              let H := (BitVec.slice __opcode 10 1)
              let Zn := (BitVec.slice __opcode 5 5)
              let Zd := (BitVec.slice __opcode 0 5)
              (decode_UZP1_Z_ZZ_Q Zm H Zn Zd)
              (pure false))
          else
            (do
              let w__779 ← (( do
                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b00000101101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                         __opcode 15 10)) == (0b000011#6 : (BitVec 6)))) : Bool) : Bool)
                then
                  (do
                    let w__778 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__778 <b 1426) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__779 : Bool)
              then
                (do
                  writeReg SEE 1426
                  let Zm := (BitVec.slice __opcode 16 5)
                  let H := (BitVec.slice __opcode 10 1)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let Zd := (BitVec.slice __opcode 0 5)
                  (decode_UZP2_Z_ZZ_Q Zm H Zn Zd)
                  (pure false))
              else
                (do
                  let w__781 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                             __opcode 21 13)) == (0b110000101#9 : (BitVec 9)))) : Bool) : Bool)
                    then
                      (do
                        let w__780 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__780 <b 1427) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__781 : Bool)
                  then
                    (do
                      writeReg SEE 1427
                      let size := (BitVec.slice __opcode 22 2)
                      let B := (BitVec.slice __opcode 16 1)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Zm := (BitVec.slice __opcode 5 5)
                      let Rdn := (BitVec.slice __opcode 0 5)
                      (decode_CLASTA_R_P_Z__ size B Pg Zm Rdn)
                      (pure false))
                  else
                    (do
                      let w__783 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                 __opcode 21 13)) == (0b110001101#9 : (BitVec 9)))) : Bool) : Bool)
                        then
                          (do
                            let w__782 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__782 <b 1428) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__783 : Bool)
                      then
                        (do
                          writeReg SEE 1428
                          let size := (BitVec.slice __opcode 22 2)
                          let B := (BitVec.slice __opcode 16 1)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Zm := (BitVec.slice __opcode 5 5)
                          let Rdn := (BitVec.slice __opcode 0 5)
                          (decode_CLASTB_R_P_Z__ size B Pg Zm Rdn)
                          (pure false))
                      else
                        (do
                          let w__785 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                     __opcode 21 13)) == (0b101010100#9 : (BitVec 9)))) : Bool) : Bool)
                            then
                              (do
                                let w__784 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__784 <b 1429) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__785 : Bool)
                          then
                            (do
                              writeReg SEE 1429
                              let size := (BitVec.slice __opcode 22 2)
                              let B := (BitVec.slice __opcode 16 1)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Zm := (BitVec.slice __opcode 5 5)
                              let Vdn := (BitVec.slice __opcode 0 5)
                              (decode_CLASTA_V_P_Z__ size B Pg Zm Vdn)
                              (pure false))
                          else
                            (do
                              let w__787 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 21 13)) == (0b101011100#9 : (BitVec 9)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__786 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__786 <b 1430) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__787 : Bool)
                              then
                                (do
                                  writeReg SEE 1430
                                  let size := (BitVec.slice __opcode 22 2)
                                  let B := (BitVec.slice __opcode 16 1)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Zm := (BitVec.slice __opcode 5 5)
                                  let Vdn := (BitVec.slice __opcode 0 5)
                                  (decode_CLASTB_V_P_Z__ size B Pg Zm Vdn)
                                  (pure false))
                              else
                                (do
                                  let w__789 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 21 13)) == (0b101000100#9 : (BitVec 9)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__788 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__788 <b 1431) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__789 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1431
                                      let size := (BitVec.slice __opcode 22 2)
                                      let B := (BitVec.slice __opcode 16 1)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Zm := (BitVec.slice __opcode 5 5)
                                      let Zdn := (BitVec.slice __opcode 0 5)
                                      (decode_CLASTA_Z_P_ZZ__ size B Pg Zm Zdn)
                                      (pure false))
                                  else
                                    (do
                                      let w__791 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 21 13)) == (0b101001100#9 : (BitVec 9)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__790 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__790 <b 1432) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__791 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1432
                                          let size := (BitVec.slice __opcode 22 2)
                                          let B := (BitVec.slice __opcode 16 1)
                                          let Pg := (BitVec.slice __opcode 10 3)
                                          let Zm := (BitVec.slice __opcode 5 5)
                                          let Zdn := (BitVec.slice __opcode 0 5)
                                          (decode_CLASTB_Z_P_ZZ__ size B Pg Zm Zdn)
                                          (pure false))
                                      else
                                        (do
                                          let w__793 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 21 13)) == (0b100001100#9 : (BitVec 9)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__792 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__792 <b 1433) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__793 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1433
                                              let size := (BitVec.slice __opcode 22 2)
                                              let Pg := (BitVec.slice __opcode 10 3)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zd := (BitVec.slice __opcode 0 5)
                                              (decode_COMPACT_Z_P_Z__ size Pg Zn Zd)
                                              (pure false))
                                          else
                                            (do
                                              let w__795 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 21 13)) == (0b101100100#9 : (BitVec 9)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__794 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__794 <b 1434) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__795 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1434
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let Pv := (BitVec.slice __opcode 10 3)
                                                  let Zm := (BitVec.slice __opcode 5 5)
                                                  let Zdn := (BitVec.slice __opcode 0 5)
                                                  (decode_SPLICE_Z_P_ZZ_Des size Pv Zm Zdn)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__797 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 21 13)) == (0b101101100#9 : (BitVec 9)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__796 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__796 <b 1435) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__797 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1435
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let Pv := (BitVec.slice __opcode 10 3)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let Zd := (BitVec.slice __opcode 0 5)
                                                      (decode_SPLICE_Z_P_ZZ_Con size Pv Zn Zd)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__799 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b00000101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 15 13)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__798 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__798 <b 1436) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__799 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1436
                                                          let imm8h := (BitVec.slice __opcode 16 5)
                                                          let imm8l := (BitVec.slice __opcode 10 3)
                                                          let Zm := (BitVec.slice __opcode 5 5)
                                                          let Zdn := (BitVec.slice __opcode 0 5)
                                                          (decode_EXT_Z_ZI_Des imm8h imm8l Zm Zdn)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__801 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b00000101011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 15 13)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__800 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__800 <b 1437) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__801 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1437
                                                              let imm8h :=
                                                                (BitVec.slice __opcode 16 5)
                                                              let imm8l :=
                                                                (BitVec.slice __opcode 10 3)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let Zd := (BitVec.slice __opcode 0 5)
                                                              (decode_EXT_Z_ZI_Con imm8h imm8l Zn Zd)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__803 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 21 13)) == (0b101000101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__802 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__802 <b 1438) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__803 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1438
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_CPY_Z_P_R__ size Pg Rn Zd)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__805 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                             __opcode 31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 21 13)) == (0b100000100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__804 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__804 <b 1439) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__805 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1439
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let Pg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Vn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_CPY_Z_P_V__ size Pg Vn
                                                                        Zd)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__807 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 10)) == (0b001000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__806 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__806 <b 1440) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__807 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1440
                                                                          let imm2 :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let tsz :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_DUP_Z_Zi__ imm2
                                                                            tsz Zn Zd)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__809 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 21 10)) == (0x80E#12 : (BitVec 12)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__808 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__808 <b 1441) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__809 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1441
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Zd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_DUP_Z_R__ size
                                                                                Rn Zd)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__811 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 21
                                                                                         13)) == (0b100000101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__810 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__810 <b 1442) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__811 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1442
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let B :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 1)
                                                                                  let Pg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_LASTA_R_P_Z__
                                                                                    size B Pg Zn Rd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__813 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             21 13)) == (0b100001101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__812 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__812 <b 1443) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__813 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1443
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let B :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 1)
                                                                                      let Pg :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_LASTB_R_P_Z__
                                                                                        size B Pg Zn
                                                                                        Rd)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__815 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 21
                                                                                                 13)) == (0b100010100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__814 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__814 <b 1444) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__815 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1444
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let B :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 1)
                                                                                          let Pg :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 3)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Vd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_LASTA_V_P_Z__
                                                                                            size B
                                                                                            Pg Zn Vd)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__817 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     21
                                                                                                     13)) == (0b100011100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__816 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__816 <b 1445) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__817 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1445
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let B :=
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
                                                                                              let Vd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              (decode_LASTB_V_P_Z__
                                                                                                size
                                                                                                B Pg
                                                                                                Zn
                                                                                                Vd)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__819 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 23) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         9)) == (0b00000101001100000100000#23 : (BitVec 23))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         4
                                                                                                         4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__818 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__818 <b 1446) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__819 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1446
                                                                                                  let H :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      1)
                                                                                                  let Pn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      4)
                                                                                                  let Pd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_PUNPKLO_P_P__
                                                                                                    H
                                                                                                    Pn
                                                                                                    Pd)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__821 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 23) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             9)) == (0b00000101001100010100000#23 : (BitVec 23))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             4
                                                                                                             4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__820 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__820 <b 1447) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__821 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1447
                                                                                                      let H :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          1)
                                                                                                      let Pn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          4)
                                                                                                      let Pd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_PUNPKHI_P_P__
                                                                                                        H
                                                                                                        Pn
                                                                                                        Pd)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__823 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 21
                                                                                                                 13)) == (0b100110100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__822 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__822 <b 1448) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__823 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1448
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              2)
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
                                                                                                          (decode_REVW_Z_Z__
                                                                                                            size
                                                                                                            Pg
                                                                                                            Zn
                                                                                                            Zd)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__825 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     21
                                                                                                                     13)) == (0b100101100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__824 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__824 <b 1449) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__825 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1449
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
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
                                                                                                              (decode_REVH_Z_Z__
                                                                                                                size
                                                                                                                Pg
                                                                                                                Zn
                                                                                                                Zd)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__827 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         21
                                                                                                                         13)) == (0b100100100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__826 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__826 <b 1450) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__827 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1450
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
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
                                                                                                                  (decode_REVB_Z_Z__
                                                                                                                    size
                                                                                                                    Pg
                                                                                                                    Zn
                                                                                                                    Zd)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__829 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             21
                                                                                                                             10)) == (0xC8E#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__828 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__828 <b 1451) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__829 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1451
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          17
                                                                                                                          1)
                                                                                                                      let H :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
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
                                                                                                                      (decode_UUNPKLO_Z_Z__
                                                                                                                        size
                                                                                                                        U
                                                                                                                        H
                                                                                                                        Zn
                                                                                                                        Zd)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__831 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 21
                                                                                                                                 10)) == (0xCCE#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__830 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__830 <b 1452) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__831 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1452
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              17
                                                                                                                              1)
                                                                                                                          let H :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
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
                                                                                                                          (decode_UUNPKHI_Z_Z__
                                                                                                                            size
                                                                                                                            U
                                                                                                                            H
                                                                                                                            Zn
                                                                                                                            Zd)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__833 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     21
                                                                                                                                     10)) == (0xC0E#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__832 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__832 <b 1453) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__833 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1453
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  17
                                                                                                                                  1)
                                                                                                                              let H :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
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
                                                                                                                              (decode_SUNPKLO_Z_Z__
                                                                                                                                size
                                                                                                                                U
                                                                                                                                H
                                                                                                                                Zn
                                                                                                                                Zd)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__835 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         21
                                                                                                                                         10)) == (0xC4E#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__834 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__834 <b 1454) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__835 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1454
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let U :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      17
                                                                                                                                      1)
                                                                                                                                  let H :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
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
                                                                                                                                  (decode_SUNPKHI_Z_Z__
                                                                                                                                    size
                                                                                                                                    U
                                                                                                                                    H
                                                                                                                                    Zn
                                                                                                                                    Zd)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__837 ← (( do
                                                                                                                                    if (((__opcode == 0b00100101001011001001000000000000#32) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__836 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__836 <b 1455) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__837 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1455
                                                                                                                                      (decode_SETFFR_F__
                                                                                                                                        ())
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__839 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   10)) == (0x638#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   4
                                                                                                                                                   4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__838 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__838 <b 1456) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__839 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1456
                                                                                                                                          let size :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let S :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              1)
                                                                                                                                          let pattern :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let Pd :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              4)
                                                                                                                                          (decode_PTRUE_P_S__
                                                                                                                                            size
                                                                                                                                            S
                                                                                                                                            pattern
                                                                                                                                            Pd)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__841 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       21
                                                                                                                                                       10)) == (0x678#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       4
                                                                                                                                                       4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__840 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__840 <b 1457) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__841 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1457
                                                                                                                                              let size :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
                                                                                                                                              let S :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  1)
                                                                                                                                              let pattern :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let Pd :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  4)
                                                                                                                                              (decode_PTRUES_P_S__
                                                                                                                                                size
                                                                                                                                                S
                                                                                                                                                pattern
                                                                                                                                                Pd)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__843 ← (( do
                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       31
                                                                                                                                                       4)) == (0x2518E40#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__842 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__842 <b 1458) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__843 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1458
                                                                                                                                                  let S :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      1)
                                                                                                                                                  let Pd :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      4)
                                                                                                                                                  (decode_PFALSE_P__
                                                                                                                                                    S
                                                                                                                                                    Pd)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__845 ← (( do
                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 28) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           31
                                                                                                                                                           4)) == (0x2519F00#28 : (BitVec 28))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__844 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__844 <b 1459) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__845 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1459
                                                                                                                                                      let S :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          1)
                                                                                                                                                      let Pd :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          4)
                                                                                                                                                      (decode_RDFFR_P_F__
                                                                                                                                                        S
                                                                                                                                                        Pd)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__847 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 23) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 9)) == (0b00100101001010001001000#23 : (BitVec 23))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 4
                                                                                                                                                                 0)) == (0b00000#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__846 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__846 <b 1460) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__847 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1460
                                                                                                                                                          let Pn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              4)
                                                                                                                                                          (decode_WRFFR_F_P__
                                                                                                                                                            Pn)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__849 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 23) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     9)) == (0b00100101000110001111000#23 : (BitVec 23))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     4
                                                                                                                                                                     4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__848 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__848 <b 1461) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__849 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 1461
                                                                                                                                                              let S :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  22
                                                                                                                                                                  1)
                                                                                                                                                              let Pg :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  4)
                                                                                                                                                              let Pd :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  4)
                                                                                                                                                              (decode_RDFFR_P_P_F__
                                                                                                                                                                S
                                                                                                                                                                Pg
                                                                                                                                                                Pd)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__851 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 23) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         9)) == (0b00100101010110001111000#23 : (BitVec 23))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         4
                                                                                                                                                                         4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__850 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__850 <b 1462) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__851 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 1462
                                                                                                                                                                  let S :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      1)
                                                                                                                                                                  let Pg :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      5
                                                                                                                                                                      4)
                                                                                                                                                                  let Pd :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      4)
                                                                                                                                                                  (decode_RDFFRS_P_P_F__
                                                                                                                                                                    S
                                                                                                                                                                    Pg
                                                                                                                                                                    Pd)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__853 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             14)) == (0b001001010101000011#18 : (BitVec 18))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               9
                                                                                                                                                                               9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               4
                                                                                                                                                                               0)) == (0b00000#5 : (BitVec 5))))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__852 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__852 <b 1463) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__853 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 1463
                                                                                                                                                                      let S :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          22
                                                                                                                                                                          1)
                                                                                                                                                                      let Pg :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          10
                                                                                                                                                                          4)
                                                                                                                                                                      let Pn :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          5
                                                                                                                                                                          4)
                                                                                                                                                                      (decode_PTEST__P_P__
                                                                                                                                                                        S
                                                                                                                                                                        Pg
                                                                                                                                                                        Pn)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__855 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 14)) == (0b001001010001000001#18 : (BitVec 18))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 9
                                                                                                                                                                                 9)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__854 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__854 <b 1464) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__855 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 1464
                                                                                                                                                                          let B :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              23
                                                                                                                                                                              1)
                                                                                                                                                                          let S :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              22
                                                                                                                                                                              1)
                                                                                                                                                                          let Pg :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              10
                                                                                                                                                                              4)
                                                                                                                                                                          let Pn :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              5
                                                                                                                                                                              4)
                                                                                                                                                                          let M :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              4
                                                                                                                                                                              1)
                                                                                                                                                                          let Pd :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              4)
                                                                                                                                                                          (decode_BRKA_P_P_P__
                                                                                                                                                                            B
                                                                                                                                                                            S
                                                                                                                                                                            Pg
                                                                                                                                                                            Pn
                                                                                                                                                                            M
                                                                                                                                                                            Pd)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__857 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     31
                                                                                                                                                                                     14)) == (0b001001010101000001#18 : (BitVec 18))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       9
                                                                                                                                                                                       9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       4
                                                                                                                                                                                       4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__856 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__856 <b 1465) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__857 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 1465
                                                                                                                                                                              let B :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  23
                                                                                                                                                                                  1)
                                                                                                                                                                              let S :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  22
                                                                                                                                                                                  1)
                                                                                                                                                                              let Pg :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  10
                                                                                                                                                                                  4)
                                                                                                                                                                              let Pn :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  5
                                                                                                                                                                                  4)
                                                                                                                                                                              let M :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  4
                                                                                                                                                                                  1)
                                                                                                                                                                              let Pd :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  0
                                                                                                                                                                                  4)
                                                                                                                                                                              (decode_BRKAS_P_P_P_Z
                                                                                                                                                                                B
                                                                                                                                                                                S
                                                                                                                                                                                Pg
                                                                                                                                                                                Pn
                                                                                                                                                                                M
                                                                                                                                                                                Pd)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__859 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         31
                                                                                                                                                                                         14)) == (0b001001011001000001#18 : (BitVec 18))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         9
                                                                                                                                                                                         9)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__858 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__858 <b 1466) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__859 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 1466
                                                                                                                                                                                  let B :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      23
                                                                                                                                                                                      1)
                                                                                                                                                                                  let S :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      22
                                                                                                                                                                                      1)
                                                                                                                                                                                  let Pg :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      10
                                                                                                                                                                                      4)
                                                                                                                                                                                  let Pn :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      5
                                                                                                                                                                                      4)
                                                                                                                                                                                  let M :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      4
                                                                                                                                                                                      1)
                                                                                                                                                                                  let Pd :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      0
                                                                                                                                                                                      4)
                                                                                                                                                                                  (decode_BRKB_P_P_P__
                                                                                                                                                                                    B
                                                                                                                                                                                    S
                                                                                                                                                                                    Pg
                                                                                                                                                                                    Pn
                                                                                                                                                                                    M
                                                                                                                                                                                    Pd)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  let w__861 ← (( do
                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 18) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             31
                                                                                                                                                                                             14)) == (0b001001011101000001#18 : (BitVec 18))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                               __opcode
                                                                                                                                                                                               9
                                                                                                                                                                                               9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                               __opcode
                                                                                                                                                                                               4
                                                                                                                                                                                               4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        let w__860 ← (( do
                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                          )
                                                                                                                                                                                          :
                                                                                                                                                                                          SailM
                                                                                                                                                                                          Int
                                                                                                                                                                                          )
                                                                                                                                                                                        (pure (((w__860 <b 1467) : Bool))))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure false)
                                                                                                                                                                                    )
                                                                                                                                                                                    :
                                                                                                                                                                                    SailM
                                                                                                                                                                                    Bool
                                                                                                                                                                                    )
                                                                                                                                                                                  if (w__861 : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 1467
                                                                                                                                                                                      let B :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          23
                                                                                                                                                                                          1)
                                                                                                                                                                                      let S :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          22
                                                                                                                                                                                          1)
                                                                                                                                                                                      let Pg :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          10
                                                                                                                                                                                          4)
                                                                                                                                                                                      let Pn :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          5
                                                                                                                                                                                          4)
                                                                                                                                                                                      let M :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          4
                                                                                                                                                                                          1)
                                                                                                                                                                                      let Pd :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          0
                                                                                                                                                                                          4)
                                                                                                                                                                                      (decode_BRKBS_P_P_P_Z
                                                                                                                                                                                        B
                                                                                                                                                                                        S
                                                                                                                                                                                        Pg
                                                                                                                                                                                        Pn
                                                                                                                                                                                        M
                                                                                                                                                                                        Pd)
                                                                                                                                                                                      (pure false))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      let w__863 ← (( do
                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 31
                                                                                                                                                                                                 20)) == (0x250#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                   15
                                                                                                                                                                                                   14)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     9
                                                                                                                                                                                                     9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     4
                                                                                                                                                                                                     4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (do
                                                                                                                                                                                            let w__862 ← (( do
                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                              )
                                                                                                                                                                                              :
                                                                                                                                                                                              SailM
                                                                                                                                                                                              Int
                                                                                                                                                                                              )
                                                                                                                                                                                            (pure (((w__862 <b 1468) : Bool))))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure false)
                                                                                                                                                                                        )
                                                                                                                                                                                        :
                                                                                                                                                                                        SailM
                                                                                                                                                                                        Bool
                                                                                                                                                                                        )
                                                                                                                                                                                      if (w__863 : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 1468
                                                                                                                                                                                          let S :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              22
                                                                                                                                                                                              1)
                                                                                                                                                                                          let Pm :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              16
                                                                                                                                                                                              4)
                                                                                                                                                                                          let Pg :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              10
                                                                                                                                                                                              4)
                                                                                                                                                                                          let Pn :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              5
                                                                                                                                                                                              4)
                                                                                                                                                                                          let Pd :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              0
                                                                                                                                                                                              4)
                                                                                                                                                                                          (decode_AND_P_P_PP_Z
                                                                                                                                                                                            S
                                                                                                                                                                                            Pm
                                                                                                                                                                                            Pg
                                                                                                                                                                                            Pn
                                                                                                                                                                                            Pd)
                                                                                                                                                                                          (pure false))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          let w__865 ← (( do
                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     31
                                                                                                                                                                                                     20)) == (0x254#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                       15
                                                                                                                                                                                                       14)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         9
                                                                                                                                                                                                         9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         4
                                                                                                                                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                            then
                                                                                                                                                                                              (do
                                                                                                                                                                                                let w__864 ← (( do
                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                  )
                                                                                                                                                                                                  :
                                                                                                                                                                                                  SailM
                                                                                                                                                                                                  Int
                                                                                                                                                                                                  )
                                                                                                                                                                                                (pure (((w__864 <b 1469) : Bool))))
                                                                                                                                                                                            else
                                                                                                                                                                                              (pure false)
                                                                                                                                                                                            )
                                                                                                                                                                                            :
                                                                                                                                                                                            SailM
                                                                                                                                                                                            Bool
                                                                                                                                                                                            )
                                                                                                                                                                                          if (w__865 : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 1469
                                                                                                                                                                                              let S :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  22
                                                                                                                                                                                                  1)
                                                                                                                                                                                              let Pm :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  16
                                                                                                                                                                                                  4)
                                                                                                                                                                                              let Pg :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  10
                                                                                                                                                                                                  4)
                                                                                                                                                                                              let Pn :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  5
                                                                                                                                                                                                  4)
                                                                                                                                                                                              let Pd :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  0
                                                                                                                                                                                                  4)
                                                                                                                                                                                              (decode_ANDS_P_P_PP_Z
                                                                                                                                                                                                S
                                                                                                                                                                                                Pm
                                                                                                                                                                                                Pg
                                                                                                                                                                                                Pn
                                                                                                                                                                                                Pd)
                                                                                                                                                                                              (pure false))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              let w__867 ← (( do
                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         31
                                                                                                                                                                                                         20)) == (0x250#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                           15
                                                                                                                                                                                                           14)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             9
                                                                                                                                                                                                             9)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             4
                                                                                                                                                                                                             4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                                                                                then
                                                                                                                                                                                                  (do
                                                                                                                                                                                                    let w__866 ← (( do
                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                      )
                                                                                                                                                                                                      :
                                                                                                                                                                                                      SailM
                                                                                                                                                                                                      Int
                                                                                                                                                                                                      )
                                                                                                                                                                                                    (pure (((w__866 <b 1470) : Bool))))
                                                                                                                                                                                                else
                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                )
                                                                                                                                                                                                :
                                                                                                                                                                                                SailM
                                                                                                                                                                                                Bool
                                                                                                                                                                                                )
                                                                                                                                                                                              if (w__867 : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg SEE 1470
                                                                                                                                                                                                  let S :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      22
                                                                                                                                                                                                      1)
                                                                                                                                                                                                  let Pm :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      16
                                                                                                                                                                                                      4)
                                                                                                                                                                                                  let Pg :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      10
                                                                                                                                                                                                      4)
                                                                                                                                                                                                  let Pn :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      5
                                                                                                                                                                                                      4)
                                                                                                                                                                                                  let Pd :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      0
                                                                                                                                                                                                      4)
                                                                                                                                                                                                  (decode_BIC_P_P_PP_Z
                                                                                                                                                                                                    S
                                                                                                                                                                                                    Pm
                                                                                                                                                                                                    Pg
                                                                                                                                                                                                    Pn
                                                                                                                                                                                                    Pd)
                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                              else
                                                                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
