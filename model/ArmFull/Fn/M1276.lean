import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1050
import ArmFull.Fn.M1051
import ArmFull.Fn.M1052
import ArmFull.Fn.M1093
import ArmFull.Fn.M1145
import ArmFull.Fn.M1146

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
def __DecodeT32__seg8 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__614 ← (( do
    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
               __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 11 11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 9 8)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 4 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
    then
      (do
        let w__613 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__613 <b 3519) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__614 : Bool)
  then
    (do
      writeReg SEE 3519
      let U := (BitVec.slice __opcode 28 1)
      let D := (BitVec.slice __opcode 22 1)
      let size := (BitVec.slice __opcode 20 2)
      let Vn := (BitVec.slice __opcode 16 4)
      let Vd := (BitVec.slice __opcode 12 4)
      let op := (BitVec.slice __opcode 10 1)
      let N := (BitVec.slice __opcode 7 1)
      let M := (BitVec.slice __opcode 5 1)
      let Vm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_VMLA_s_T2enc_A_txt U D size Vn Vd op N M Vm)
      (pure false))
  else
    (do
      let w__616 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                   __opcode 21 16)) == (0b110000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                     __opcode 11 6)) == (0b101001#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
        then
          (do
            let w__615 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__615 <b 3521) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__616 : Bool)
      then
        (do
          writeReg SEE 3521
          let D := (BitVec.slice __opcode 22 1)
          let Vd := (BitVec.slice __opcode 12 4)
          let M := (BitVec.slice __opcode 5 1)
          let Vm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_VMOVX_T1enc_A_txt D Vd M Vm)
          (pure false))
      else
        (do
          let w__618 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                       __opcode 21 16)) == (0b110000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                         __opcode 11 6)) == (0b101011#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
            then
              (do
                let w__617 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__617 <b 3523) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__618 : Bool)
          then
            (do
              writeReg SEE 3523
              let D := (BitVec.slice __opcode 22 1)
              let Vd := (BitVec.slice __opcode 12 4)
              let M := (BitVec.slice __opcode 5 1)
              let Vm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_VINS_T1enc_A_txt D Vd M Vm)
              (pure false))
          else
            (do
              let w__620 ← (( do
                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11101100010#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                           __opcode 11 6)) == (0b101100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    let w__619 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__619 <b 3525) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__620 : Bool)
              then
                (do
                  writeReg SEE 3525
                  let op := (BitVec.slice __opcode 20 1)
                  let Rt2 := (BitVec.slice __opcode 16 4)
                  let Rt := (BitVec.slice __opcode 12 4)
                  let M := (BitVec.slice __opcode 5 1)
                  let Vm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_VMOV_d_T1enc_A_txt op Rt2 Rt M Vm)
                  (pure false))
              else
                (do
                  let w__622 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                               __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 21 19)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 11 11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     __opcode 8 7)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     __opcode 5 4)) == (0b01#2 : (BitVec 2)))))))) : Bool) : Bool)
                    then
                      (do
                        let w__621 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__621 <b 3531) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__622 : Bool)
                  then
                    (do
                      writeReg SEE 3531
                      let i := (BitVec.slice __opcode 28 1)
                      let D := (BitVec.slice __opcode 22 1)
                      let imm3 := (BitVec.slice __opcode 16 3)
                      let Vd := (BitVec.slice __opcode 12 4)
                      let cmode := (BitVec.slice __opcode 8 4)
                      let Q := (BitVec.slice __opcode 6 1)
                      let op := (BitVec.slice __opcode 5 1)
                      let imm4 := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_VMOV_i_T1enc_A_txt i D imm3 Vd cmode Q op imm4)
                      (pure false))
                  else
                    (do
                      let w__624 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     __opcode 11 10)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                     __opcode 7 4)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
                        then
                          (do
                            let w__623 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__623 <b 3532) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__624 : Bool)
                      then
                        (do
                          writeReg SEE 3532
                          let D := (BitVec.slice __opcode 22 1)
                          let imm4H := (BitVec.slice __opcode 16 4)
                          let Vd := (BitVec.slice __opcode 12 4)
                          let size := (BitVec.slice __opcode 8 2)
                          let imm4L := (BitVec.slice __opcode 0 4)
                          if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 7)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 5)])) != 0#1)) : Bool)
                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                          else
                            (do
                              (decode_aarch32_instrs_VMOV_i_T2enc_A_txt D imm4H Vd size imm4L))
                          (pure false))
                      else
                        (do
                          let w__626 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb __opcode
                                     31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                       __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 21 19)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                             __opcode 8 7)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                             __opcode 5 4)) == (0b01#2 : (BitVec 2)))))))) : Bool) : Bool)
                            then
                              (do
                                let w__625 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__625 <b 3533) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__626 : Bool)
                          then
                            (do
                              writeReg SEE 3533
                              let i := (BitVec.slice __opcode 28 1)
                              let D := (BitVec.slice __opcode 22 1)
                              let imm3 := (BitVec.slice __opcode 16 3)
                              let Vd := (BitVec.slice __opcode 12 4)
                              let cmode := (BitVec.slice __opcode 8 4)
                              let Q := (BitVec.slice __opcode 6 1)
                              let op := (BitVec.slice __opcode 5 1)
                              let imm4 := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_VMOV_i_T3enc_A_txt i D imm3 Vd cmode Q op imm4)
                              (pure false))
                          else
                            (do
                              let w__628 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                           __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 21 19)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 11 10)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 7 7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                 __opcode 5 4)) == (0b01#2 : (BitVec 2)))))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__627 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__627 <b 3534) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__628 : Bool)
                              then
                                (do
                                  writeReg SEE 3534
                                  let i := (BitVec.slice __opcode 28 1)
                                  let D := (BitVec.slice __opcode 22 1)
                                  let imm3 := (BitVec.slice __opcode 16 3)
                                  let Vd := (BitVec.slice __opcode 12 4)
                                  let cmode := (BitVec.slice __opcode 8 4)
                                  let Q := (BitVec.slice __opcode 6 1)
                                  let op := (BitVec.slice __opcode 5 1)
                                  let imm4 := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_VMOV_i_T4enc_A_txt i D imm3 Vd cmode Q op
                                    imm4)
                                  (pure false))
                              else
                                (do
                                  let w__630 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                               __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 21 19)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                   __opcode 11 7)) == (0b11100#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 5 4)) == (0b11#2 : (BitVec 2))))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__629 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__629 <b 3535) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__630 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3535
                                      let i := (BitVec.slice __opcode 28 1)
                                      let D := (BitVec.slice __opcode 22 1)
                                      let imm3 := (BitVec.slice __opcode 16 3)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let cmode := (BitVec.slice __opcode 8 4)
                                      let Q := (BitVec.slice __opcode 6 1)
                                      let op := (BitVec.slice __opcode 5 1)
                                      let imm4 := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_VMOV_i_T5enc_A_txt i D imm3 Vd cmode Q
                                        op imm4)
                                      (pure false))
                                  else
                                    (do
                                      let w__632 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                   __opcode 27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 18 16)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                       __opcode 11 8)) == (0xA#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 4 4)) == (1#1 : (BitVec 1)))))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__631 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__631 <b 3537) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__632 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3537
                                          let U := (BitVec.slice __opcode 28 1)
                                          let D := (BitVec.slice __opcode 22 1)
                                          let imm3H := (BitVec.slice __opcode 19 3)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let L := (BitVec.slice __opcode 7 1)
                                          let M := (BitVec.slice __opcode 5 1)
                                          let Vm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_VMOVL_T1enc_A_txt U D imm3H Vd L M
                                            Vm)
                                          (pure false))
                                      else
                                        (do
                                          let w__634 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 21 20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                         __opcode 17 16)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 11 6)) == (0b001000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__633 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__633 <b 3539) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__634 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3539
                                              let D := (BitVec.slice __opcode 22 1)
                                              let size := (BitVec.slice __opcode 18 2)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let M := (BitVec.slice __opcode 5 1)
                                              let Vm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_VMOVN_T1enc_A_txt D size Vd M
                                                Vm)
                                              (pure false))
                                          else
                                            (do
                                              let w__636 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                         __opcode 31 21)) == (0b11101110000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                           __opcode 11 8)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                           __opcode 6 0)) == (0b0010000#7 : (BitVec 7))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__635 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__635 <b 3541) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__636 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3541
                                                  let op := (BitVec.slice __opcode 20 1)
                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                  let Rt := (BitVec.slice __opcode 12 4)
                                                  let N := (BitVec.slice __opcode 7 1)
                                                  if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 5)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 3)])) != 0#1)) : Bool)
                                                  then
                                                    sailThrow ((Error_ConstrainedUnpredictable ()))
                                                  else
                                                    (do
                                                      (decode_aarch32_instrs_VMOV_h_T1enc_A_txt op
                                                        Vn Rt N))
                                                  (pure false))
                                              else
                                                (do
                                                  let w__638 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 21 16)) == (0b110000#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                 __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 7 6)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__637 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__637 <b 3543) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__638 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3543
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let size := (BitVec.slice __opcode 8 2)
                                                      let M := (BitVec.slice __opcode 5 1)
                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VMOV_r_T2enc_A_txt D Vd
                                                        size M Vm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__640 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b111011100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 20 20)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 11 8)) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                     __opcode 4 0)) == (0b10000#5 : (BitVec 5)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__639 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__639 <b 3545) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__640 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3545
                                                          let opc1 := (BitVec.slice __opcode 21 2)
                                                          let Vd := (BitVec.slice __opcode 16 4)
                                                          let Rt := (BitVec.slice __opcode 12 4)
                                                          let D := (BitVec.slice __opcode 7 1)
                                                          let opc2 := (BitVec.slice __opcode 5 2)
                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 0)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 3)])) != 0#1)) : Bool)
                                                          then
                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                              ()))
                                                          else
                                                            (do
                                                              (decode_aarch32_instrs_VMOV_rs_T1enc_A_txt
                                                                opc1 Vd Rt D opc2))
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__642 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b11101110000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                       __opcode 11 8)) == (0xA#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                       __opcode 6 0)) == (0b0010000#7 : (BitVec 7))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__641 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__641 <b 3547) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__642 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3547
                                                              let op := (BitVec.slice __opcode 20 1)
                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                              let Rt := (BitVec.slice __opcode 12 4)
                                                              let N := (BitVec.slice __opcode 7 1)
                                                              if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 5)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 6)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 3)])) != 0#1)) : Bool)
                                                              then
                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                  ()))
                                                              else
                                                                (do
                                                                  (decode_aarch32_instrs_VMOV_s_T1enc_A_txt
                                                                    op Vn Rt N))
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__644 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0xEE#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 20 20)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                             __opcode 11 8)) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                             __opcode 4 0)) == (0b10000#5 : (BitVec 5)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__643 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__643 <b 3549) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__644 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3549
                                                                  let U :=
                                                                    (BitVec.slice __opcode 23 1)
                                                                  let opc1 :=
                                                                    (BitVec.slice __opcode 21 2)
                                                                  let Vn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Rt :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let N :=
                                                                    (BitVec.slice __opcode 7 1)
                                                                  let opc2 :=
                                                                    (BitVec.slice __opcode 5 2)
                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 0)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 3)])) != 0#1)) : Bool)
                                                                  then
                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                      ()))
                                                                  else
                                                                    (do
                                                                      (decode_aarch32_instrs_VMOV_sr_T1enc_A_txt
                                                                        U opc1 Vn Rt N opc2))
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__646 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                             __opcode 31 21)) == (0b11101100010#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 11 6)) == (0b101000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__645 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__645 <b 3551) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__646 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3551
                                                                      let op :=
                                                                        (BitVec.slice __opcode 20 1)
                                                                      let Rt2 :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rt :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 5 1)
                                                                      let Vm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VMOV_ss_T1enc_A_txt
                                                                        op Rt2 Rt M Vm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__648 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b111111110#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 11 8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__647 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__647 <b 3554) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__648 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3554
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let sz :=
                                                                            (BitVec.slice __opcode
                                                                              20 1)
                                                                          let Vn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Vd :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let N :=
                                                                            (BitVec.slice __opcode 7
                                                                              1)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode 6
                                                                              1)
                                                                          let M :=
                                                                            (BitVec.slice __opcode 5
                                                                              1)
                                                                          let Vm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_VMUL_f_T1enc_A_txt
                                                                            D sz Vn Vd N Q M Vm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__650 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b111011100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                         __opcode 11
                                                                                         10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__649 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__649 <b 3555) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__650 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3555
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let Vn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Vd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 8 2)
                                                                              let N :=
                                                                                (BitVec.slice
                                                                                  __opcode 7 1)
                                                                              let M :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 1)
                                                                              let Vm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_VMUL_f_T2enc_A_txt
                                                                                D Vn Vd size N M Vm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__652 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           27 23)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 8)) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__651 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__651 <b 3558) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__652 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3558
                                                                                  let op :=
                                                                                    (BitVec.slice
                                                                                      __opcode 28 1)
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 20 2)
                                                                                  let Vn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Vd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let N :=
                                                                                    (BitVec.slice
                                                                                      __opcode 7 1)
                                                                                  let Q :=
                                                                                    (BitVec.slice
                                                                                      __opcode 6 1)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 1)
                                                                                  let Vm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VMUL_i_T1enc_A_txt
                                                                                    op D size Vn Vd
                                                                                    N Q M Vm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__654 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               27 23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 11
                                                                                                 10)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   8
                                                                                                   8)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     6
                                                                                                     6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     4
                                                                                                     4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__653 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__653 <b 3559) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__654 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3559
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          28 1)
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          20 2)
                                                                                      let Vn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Vd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let op :=
                                                                                        (BitVec.slice
                                                                                          __opcode 9
                                                                                          1)
                                                                                      let N :=
                                                                                        (BitVec.slice
                                                                                          __opcode 7
                                                                                          1)
                                                                                      let M :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          1)
                                                                                      let Vm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_VMUL_i_T2enc_A_txt
                                                                                        U D size Vn
                                                                                        Vd op N M Vm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__656 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   27
                                                                                                   23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     11
                                                                                                     9)) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       6
                                                                                                       6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       4
                                                                                                       4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__655 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__655 <b 3562) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__656 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3562
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              28 1)
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              20 2)
                                                                                          let Vn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Vd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let F :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              8 1)
                                                                                          let N :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              7 1)
                                                                                          let M :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 1)
                                                                                          let Vm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_VMUL_s_T1enc_A_txt
                                                                                            Q D size
                                                                                            Vn Vd F
                                                                                            N M Vm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__658 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       27
                                                                                                       23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         11
                                                                                                         8)) == (0xA#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           6
                                                                                                           6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           4
                                                                                                           4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__657 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__657 <b 3563) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__658 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3563
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
                                                                                              (decode_aarch32_instrs_VMUL_s_T2enc_A_txt
                                                                                                U D
                                                                                                size
                                                                                                Vn
                                                                                                Vd N
                                                                                                M Vm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__660 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           27
                                                                                                           23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             21
                                                                                                             19)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               11
                                                                                                               11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 8
                                                                                                                 7)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 5
                                                                                                                 4)) == (0b11#2 : (BitVec 2)))))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__659 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__659 <b 3567) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__660 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3567
                                                                                                  let i :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      28
                                                                                                      1)
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let imm3 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      3)
                                                                                                  let Vd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let cmode :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      8
                                                                                                      4)
                                                                                                  let Q :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      6
                                                                                                      1)
                                                                                                  let imm4 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_VMVN_i_T1enc_A_txt
                                                                                                    i
                                                                                                    D
                                                                                                    imm3
                                                                                                    Vd
                                                                                                    cmode
                                                                                                    Q
                                                                                                    imm4)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__662 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               27
                                                                                                               23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 21
                                                                                                                 19)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   11
                                                                                                                   10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     8
                                                                                                                     7)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     5
                                                                                                                     4)) == (0b11#2 : (BitVec 2)))))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__661 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__661 <b 3568) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__662 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3568
                                                                                                      let i :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          28
                                                                                                          1)
                                                                                                      let D :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let imm3 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          3)
                                                                                                      let Vd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let cmode :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          8
                                                                                                          4)
                                                                                                      let Q :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          6
                                                                                                          1)
                                                                                                      let imm4 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_aarch32_instrs_VMVN_i_T2enc_A_txt
                                                                                                        i
                                                                                                        D
                                                                                                        imm3
                                                                                                        Vd
                                                                                                        cmode
                                                                                                        Q
                                                                                                        imm4)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__664 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 29)) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   27
                                                                                                                   23)) == (0b11111#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     21
                                                                                                                     19)) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       11
                                                                                                                       9)) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         7
                                                                                                                         7)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         5
                                                                                                                         4)) == (0b11#2 : (BitVec 2)))))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__663 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__663 <b 3569) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__664 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3569
                                                                                                          let i :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              28
                                                                                                              1)
                                                                                                          let D :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let imm3 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              3)
                                                                                                          let Vd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              4)
                                                                                                          let cmode :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              8
                                                                                                              4)
                                                                                                          let Q :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              6
                                                                                                              1)
                                                                                                          let imm4 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_VMVN_i_T3enc_A_txt
                                                                                                            i
                                                                                                            D
                                                                                                            imm3
                                                                                                            Vd
                                                                                                            cmode
                                                                                                            Q
                                                                                                            imm4)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__666 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         17
                                                                                                                         16)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           11
                                                                                                                           7)) == (0b01011#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           4
                                                                                                                           4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__665 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__665 <b 3571) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__666 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3571
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
                                                                                                              (decode_aarch32_instrs_VMVN_r_T1enc_A_txt
                                                                                                                D
                                                                                                                size
                                                                                                                Vd
                                                                                                                Q
                                                                                                                M
                                                                                                                Vm)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__668 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             17
                                                                                                                             16)) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               11
                                                                                                                               11)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 9
                                                                                                                                 7)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 4
                                                                                                                                 4)) == (0#1 : (BitVec 1)))))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__667 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__667 <b 3574) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__668 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3574
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
                                                                                                                  let F :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
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
                                                                                                                  (decode_aarch32_instrs_VNEG_T1enc_A_txt
                                                                                                                    D
                                                                                                                    size
                                                                                                                    Vd
                                                                                                                    F
                                                                                                                    Q
                                                                                                                    M
                                                                                                                    Vm)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (pure true))))))))))))))))))))))))))))


end ArmFull.Functions
