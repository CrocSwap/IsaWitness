import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1059
import ArmFull.Fn.M1147
import ArmFull.Fn.M1288
import ArmFull.Fn.M1289
import ArmFull.Fn.M1290

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
def __DecodeT32__seg11 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__788 ← (( do
    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 11 8)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
    then
      (do
        let w__787 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__787 <b 3695) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__788 : Bool)
  then
    (do
      writeReg SEE 3695
      let D := (BitVec.slice __opcode 22 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let Vd := (BitVec.slice __opcode 12 4)
      let size := (BitVec.slice __opcode 10 2)
      let index_align := (BitVec.slice __opcode 4 4)
      let Rm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_VST1_1_T1enc_A_txt D Rn Vd size index_align Rm)
      (pure false))
  else
    (do
      let w__790 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 11 8)) == (0x4#4 : (BitVec 4))))) : Bool) : Bool)
        then
          (do
            let w__789 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__789 <b 3696) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__790 : Bool)
      then
        (do
          writeReg SEE 3696
          let D := (BitVec.slice __opcode 22 1)
          let Rn := (BitVec.slice __opcode 16 4)
          let Vd := (BitVec.slice __opcode 12 4)
          let size := (BitVec.slice __opcode 10 2)
          let index_align := (BitVec.slice __opcode 4 4)
          let Rm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_VST1_1_T2enc_A_txt D Rn Vd size index_align Rm)
          (pure false))
      else
        (do
          let w__792 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                       __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                       __opcode 11 8)) == (0x8#4 : (BitVec 4))))) : Bool) : Bool)
            then
              (do
                let w__791 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__791 <b 3697) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__792 : Bool)
          then
            (do
              writeReg SEE 3697
              let D := (BitVec.slice __opcode 22 1)
              let Rn := (BitVec.slice __opcode 16 4)
              let Vd := (BitVec.slice __opcode 12 4)
              let size := (BitVec.slice __opcode 10 2)
              let index_align := (BitVec.slice __opcode 4 4)
              let Rm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_VST1_1_T3enc_A_txt D Rn Vd size index_align Rm)
              (pure false))
          else
            (do
              let w__794 ← (( do
                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                           __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                           __opcode 11 8)) == (0x7#4 : (BitVec 4))))) : Bool) : Bool)
                then
                  (do
                    let w__793 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__793 <b 3702) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__794 : Bool)
              then
                (do
                  writeReg SEE 3702
                  let D := (BitVec.slice __opcode 22 1)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Vd := (BitVec.slice __opcode 12 4)
                  let itype := (BitVec.slice __opcode 8 4)
                  let size := (BitVec.slice __opcode 6 2)
                  let align := (BitVec.slice __opcode 4 2)
                  let Rm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_VST1_m_T1enc_A_txt D Rn Vd itype size align Rm)
                  (pure false))
              else
                (do
                  let w__796 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                               __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                               __opcode 11 8)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                    then
                      (do
                        let w__795 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__795 <b 3703) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__796 : Bool)
                  then
                    (do
                      writeReg SEE 3703
                      let D := (BitVec.slice __opcode 22 1)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let Vd := (BitVec.slice __opcode 12 4)
                      let itype := (BitVec.slice __opcode 8 4)
                      let size := (BitVec.slice __opcode 6 2)
                      let align := (BitVec.slice __opcode 4 2)
                      let Rm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_VST1_m_T2enc_A_txt D Rn Vd itype size align Rm)
                      (pure false))
                  else
                    (do
                      let w__798 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                   __opcode 11 8)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                        then
                          (do
                            let w__797 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__797 <b 3704) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__798 : Bool)
                      then
                        (do
                          writeReg SEE 3704
                          let D := (BitVec.slice __opcode 22 1)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Vd := (BitVec.slice __opcode 12 4)
                          let itype := (BitVec.slice __opcode 8 4)
                          let size := (BitVec.slice __opcode 6 2)
                          let align := (BitVec.slice __opcode 4 2)
                          let Rm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_VST1_m_T3enc_A_txt D Rn Vd itype size align Rm)
                          (pure false))
                      else
                        (do
                          let w__800 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                       __opcode 11 8)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
                            then
                              (do
                                let w__799 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__799 <b 3705) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__800 : Bool)
                          then
                            (do
                              writeReg SEE 3705
                              let D := (BitVec.slice __opcode 22 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Vd := (BitVec.slice __opcode 12 4)
                              let itype := (BitVec.slice __opcode 8 4)
                              let size := (BitVec.slice __opcode 6 2)
                              let align := (BitVec.slice __opcode 4 2)
                              let Rm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_VST1_m_T4enc_A_txt D Rn Vd itype size align Rm)
                              (pure false))
                          else
                            (do
                              let w__802 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                           __opcode 11 8)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__801 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__801 <b 3709) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__802 : Bool)
                              then
                                (do
                                  writeReg SEE 3709
                                  let D := (BitVec.slice __opcode 22 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Vd := (BitVec.slice __opcode 12 4)
                                  let size := (BitVec.slice __opcode 10 2)
                                  let index_align := (BitVec.slice __opcode 4 4)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_VST2_1_T1enc_A_txt D Rn Vd size index_align
                                    Rm)
                                  (pure false))
                              else
                                (do
                                  let w__804 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                               __opcode 11 8)) == (0x5#4 : (BitVec 4))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__803 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__803 <b 3710) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__804 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3710
                                      let D := (BitVec.slice __opcode 22 1)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let size := (BitVec.slice __opcode 10 2)
                                      let index_align := (BitVec.slice __opcode 4 4)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_VST2_1_T2enc_A_txt D Rn Vd size
                                        index_align Rm)
                                      (pure false))
                                  else
                                    (do
                                      let w__806 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   __opcode 11 8)) == (0x9#4 : (BitVec 4))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__805 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__805 <b 3711) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__806 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3711
                                          let D := (BitVec.slice __opcode 22 1)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let size := (BitVec.slice __opcode 10 2)
                                          let index_align := (BitVec.slice __opcode 4 4)
                                          let Rm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_VST2_1_T3enc_A_txt D Rn Vd size
                                            index_align Rm)
                                          (pure false))
                                      else
                                        (do
                                          let w__808 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                       __opcode 11 9)) == (0b100#3 : (BitVec 3))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__807 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__807 <b 3714) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__808 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3714
                                              let D := (BitVec.slice __opcode 22 1)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let itype := (BitVec.slice __opcode 8 4)
                                              let size := (BitVec.slice __opcode 6 2)
                                              let align := (BitVec.slice __opcode 4 2)
                                              let Rm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_VST2_m_T1enc_A_txt D Rn Vd
                                                itype size align Rm)
                                              (pure false))
                                          else
                                            (do
                                              let w__810 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                           __opcode 11 8)) == (0x3#4 : (BitVec 4))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__809 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__809 <b 3715) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__810 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3715
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let itype := (BitVec.slice __opcode 8 4)
                                                  let size := (BitVec.slice __opcode 6 2)
                                                  let align := (BitVec.slice __opcode 4 2)
                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_VST2_m_T2enc_A_txt D Rn Vd
                                                    itype size align Rm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__812 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                               __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                               __opcode 11 8)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__811 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__811 <b 3719) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__812 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3719
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let size := (BitVec.slice __opcode 10 2)
                                                      let index_align := (BitVec.slice __opcode 4 4)
                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VST3_1_T1enc_A_txt D Rn
                                                        Vd size index_align Rm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__814 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                   __opcode 11 8)) == (0x6#4 : (BitVec 4))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__813 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__813 <b 3720) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__814 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3720
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let size := (BitVec.slice __opcode 10 2)
                                                          let index_align :=
                                                            (BitVec.slice __opcode 4 4)
                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VST3_1_T2enc_A_txt
                                                            D Rn Vd size index_align Rm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__816 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                       __opcode 11 8)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__815 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__815 <b 3721) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__816 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3721
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let size :=
                                                                (BitVec.slice __opcode 10 2)
                                                              let index_align :=
                                                                (BitVec.slice __opcode 4 4)
                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VST3_1_T3enc_A_txt
                                                                D Rn Vd size index_align Rm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__818 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                           __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 11 9)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__817 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__817 <b 3723) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__818 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3723
                                                                  let D :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Vd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let itype :=
                                                                    (BitVec.slice __opcode 8 4)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 6 2)
                                                                  let align :=
                                                                    (BitVec.slice __opcode 4 2)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_VST3_m_T1enc_A_txt
                                                                    D Rn Vd itype size align Rm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__820 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                               __opcode 11 8)) == (0x3#4 : (BitVec 4))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__819 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__819 <b 3727) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__820 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3727
                                                                      let D :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Vd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 10 2)
                                                                      let index_align :=
                                                                        (BitVec.slice __opcode 4 4)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VST4_1_T1enc_A_txt
                                                                        D Rn Vd size index_align Rm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__822 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                   __opcode 11 8)) == (0x7#4 : (BitVec 4))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__821 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__821 <b 3728) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__822 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3728
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Vd :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              10 2)
                                                                          let index_align :=
                                                                            (BitVec.slice __opcode 4
                                                                              4)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_VST4_1_T2enc_A_txt
                                                                            D Rn Vd size index_align
                                                                            Rm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__824 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b111110011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                       __opcode 11 8)) == (0xB#4 : (BitVec 4))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__823 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__823 <b 3729) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__824 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3729
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Vd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 2)
                                                                              let index_align :=
                                                                                (BitVec.slice
                                                                                  __opcode 4 4)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_VST4_1_T3enc_A_txt
                                                                                D Rn Vd size
                                                                                index_align Rm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__826 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b111110010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           11 9)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__825 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__825 <b 3731) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__826 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3731
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Vd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let itype :=
                                                                                    (BitVec.slice
                                                                                      __opcode 8 4)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 6 2)
                                                                                  let align :=
                                                                                    (BitVec.slice
                                                                                      __opcode 4 2)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VST4_m_T1enc_A_txt
                                                                                    D Rn Vd itype
                                                                                    size align Rm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__828 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 25)) == (0b1110110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               20 20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               11 8)) == (0xB#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__827 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__827 <b 3734) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__828 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3734
                                                                                      let P :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          24 1)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          23 1)
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let W :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          21 1)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Vd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let imm8 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          8)
                                                                                      (decode_aarch32_instrs_VSTM_T1enc_A_txt
                                                                                        P U D W Rn
                                                                                        Vd imm8)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__830 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 25)) == (0b1110110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   20
                                                                                                   20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   11
                                                                                                   8)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__829 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__829 <b 3735) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__830 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3735
                                                                                          let P :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              24 1)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              23 1)
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let W :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              21 1)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Vd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let imm8 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 8)
                                                                                          (decode_aarch32_instrs_VSTM_T2enc_A_txt
                                                                                            P U D W
                                                                                            Rn Vd
                                                                                            imm8)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__832 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0xED#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       11
                                                                                                       10)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__831 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__831 <b 3737) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__832 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3737
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  23
                                                                                                  1)
                                                                                              let D :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Vd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  4)
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  8
                                                                                                  2)
                                                                                              let imm8 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  8)
                                                                                              (decode_aarch32_instrs_VSTR_T1enc_A_txt
                                                                                                U D
                                                                                                Rn
                                                                                                Vd
                                                                                                size
                                                                                                imm8)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__834 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             11
                                                                                                             8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             4
                                                                                                             4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__833 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__833 <b 3740) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__834 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3740
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let sz :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      20
                                                                                                      1)
                                                                                                  let Vn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Vd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let N :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      7
                                                                                                      1)
                                                                                                  let Q :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      6
                                                                                                      1)
                                                                                                  let M :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      1)
                                                                                                  let Vm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_VSUB_f_T1enc_A_txt
                                                                                                    D
                                                                                                    sz
                                                                                                    Vn
                                                                                                    Vd
                                                                                                    N
                                                                                                    Q
                                                                                                    M
                                                                                                    Vm)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__836 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             23)) == (0b111011100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 11
                                                                                                                 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   6
                                                                                                                   6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   4
                                                                                                                   4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__835 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__835 <b 3741) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__836 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3741
                                                                                                      let D :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let Vn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let Vd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          8
                                                                                                          2)
                                                                                                      let N :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          7
                                                                                                          1)
                                                                                                      let M :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          1)
                                                                                                      let Vm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_aarch32_instrs_VSUB_f_T2enc_A_txt
                                                                                                        D
                                                                                                        Vn
                                                                                                        Vd
                                                                                                        size
                                                                                                        N
                                                                                                        M
                                                                                                        Vm)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__838 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b111011111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   11
                                                                                                                   8)) == (0x6#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     6
                                                                                                                     6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     4
                                                                                                                     4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__837 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__837 <b 3743) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__838 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3743
                                                                                                          let D :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              20
                                                                                                              2)
                                                                                                          let Vn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let Vd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              4)
                                                                                                          let N :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              7
                                                                                                              1)
                                                                                                          let M :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              1)
                                                                                                          let Vm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_VSUBHN_T1enc_A_txt
                                                                                                            D
                                                                                                            size
                                                                                                            Vn
                                                                                                            Vd
                                                                                                            N
                                                                                                            M
                                                                                                            Vm)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__840 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       11
                                                                                                                       8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       4
                                                                                                                       4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__839 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__839 <b 3745) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__840 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3745
                                                                                                              let D :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  20
                                                                                                                  2)
                                                                                                              let Vn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let Vd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              let N :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  7
                                                                                                                  1)
                                                                                                              let Q :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  6
                                                                                                                  1)
                                                                                                              let M :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  1)
                                                                                                              let Vm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              (decode_aarch32_instrs_VSUB_i_T1enc_A_txt
                                                                                                                D
                                                                                                                size
                                                                                                                Vn
                                                                                                                Vd
                                                                                                                N
                                                                                                                Q
                                                                                                                M
                                                                                                                Vm)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__842 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           27
                                                                                                                           23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             11
                                                                                                                             9)) == (0b001#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               6
                                                                                                                               6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               4
                                                                                                                               4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__841 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__841 <b 3747) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__842 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3747
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      28
                                                                                                                      1)
                                                                                                                  let D :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      20
                                                                                                                      2)
                                                                                                                  let Vn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let Vd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      4)
                                                                                                                  let op :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      8
                                                                                                                      1)
                                                                                                                  let N :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      7
                                                                                                                      1)
                                                                                                                  let M :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      1)
                                                                                                                  let Vm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      4)
                                                                                                                  (decode_aarch32_instrs_VSUBL_T1enc_A_txt
                                                                                                                    U
                                                                                                                    D
                                                                                                                    size
                                                                                                                    Vn
                                                                                                                    Vd
                                                                                                                    op
                                                                                                                    N
                                                                                                                    M
                                                                                                                    Vm)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__844 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 17
                                                                                                                                 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   11
                                                                                                                                   7)) == (0b00000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   4
                                                                                                                                   4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__843 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__843 <b 3749) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__844 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3749
                                                                                                                      let D :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          1)
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          18
                                                                                                                          2)
                                                                                                                      let Vd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          4)
                                                                                                                      let Q :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          6
                                                                                                                          1)
                                                                                                                      let M :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          1)
                                                                                                                      let Vm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          4)
                                                                                                                      (decode_aarch32_instrs_VSWP_T1enc_A_txt
                                                                                                                        D
                                                                                                                        size
                                                                                                                        Vd
                                                                                                                        Q
                                                                                                                        M
                                                                                                                        Vm)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__846 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     11
                                                                                                                                     10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     4
                                                                                                                                     4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__845 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__845 <b 3751) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__846 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 3751
                                                                                                                          let D :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let Vn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let Vd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              4)
                                                                                                                          let len :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              8
                                                                                                                              2)
                                                                                                                          let N :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              7
                                                                                                                              1)
                                                                                                                          let op :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              6
                                                                                                                              1)
                                                                                                                          let M :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              1)
                                                                                                                          let Vm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              4)
                                                                                                                          (decode_aarch32_instrs_VTBL_T1enc_A_txt
                                                                                                                            D
                                                                                                                            Vn
                                                                                                                            Vd
                                                                                                                            len
                                                                                                                            N
                                                                                                                            op
                                                                                                                            M
                                                                                                                            Vm)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__848 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         17
                                                                                                                                         16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           11
                                                                                                                                           7)) == (0b00001#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           4
                                                                                                                                           4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__847 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__847 <b 3753) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__848 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3753
                                                                                                                              let D :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  1)
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  18
                                                                                                                                  2)
                                                                                                                              let Vd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  4)
                                                                                                                              let Q :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  6
                                                                                                                                  1)
                                                                                                                              let M :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  1)
                                                                                                                              let Vm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  4)
                                                                                                                              (decode_aarch32_instrs_VTRN_T1enc_A_txt
                                                                                                                                D
                                                                                                                                size
                                                                                                                                Vd
                                                                                                                                Q
                                                                                                                                M
                                                                                                                                Vm)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__850 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         23)) == (0b111011110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           11
                                                                                                                                           8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           4
                                                                                                                                           4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__849 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__849 <b 3755) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__850 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 3755
                                                                                                                                  let D :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      1)
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      20
                                                                                                                                      2)
                                                                                                                                  let Vn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let Vd :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      4)
                                                                                                                                  let N :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      7
                                                                                                                                      1)
                                                                                                                                  let Q :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      6
                                                                                                                                      1)
                                                                                                                                  let M :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      1)
                                                                                                                                  let Vm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      4)
                                                                                                                                  (decode_aarch32_instrs_VTST_T1enc_A_txt
                                                                                                                                    D
                                                                                                                                    size
                                                                                                                                    Vn
                                                                                                                                    Vd
                                                                                                                                    N
                                                                                                                                    Q
                                                                                                                                    M
                                                                                                                                    Vm)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__852 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 17
                                                                                                                                                 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   11
                                                                                                                                                   7)) == (0b00010#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   4
                                                                                                                                                   4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__851 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__851 <b 3757) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__852 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 3757
                                                                                                                                      let D :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          1)
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          18
                                                                                                                                          2)
                                                                                                                                      let Vd :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          12
                                                                                                                                          4)
                                                                                                                                      let Q :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          6
                                                                                                                                          1)
                                                                                                                                      let M :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          1)
                                                                                                                                      let Vm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          4)
                                                                                                                                      (decode_aarch32_instrs_VUZP_T1enc_A_txt
                                                                                                                                        D
                                                                                                                                        size
                                                                                                                                        Vd
                                                                                                                                        Q
                                                                                                                                        M
                                                                                                                                        Vm)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))


end ArmFull.Functions
