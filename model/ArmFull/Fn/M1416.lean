import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1317
import ArmFull.Fn.M1318
import ArmFull.Fn.M1319
import ArmFull.Fn.M1320

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
def __DecodeA64_SVE__seg21 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1699 ← (( do
    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b1000010001#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
             __opcode 15 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
    then
      (do
        let w__1698 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1698 <b 1886) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1699 : Bool)
  then
    (do
      writeReg SEE 1886
      let dtypeh := (BitVec.slice __opcode 23 2)
      let imm6 := (BitVec.slice __opcode 16 6)
      let dtypel := (BitVec.slice __opcode 13 2)
      let Pg := (BitVec.slice __opcode 10 3)
      let Rn := (BitVec.slice __opcode 5 5)
      let Zt := (BitVec.slice __opcode 0 5)
      (decode_LD1RB_Z_P_BI_U64 dtypeh imm6 dtypel Pg Rn Zt)
      (pure false))
  else
    (do
      let w__1701 ← (( do
        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b1000010011#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 __opcode 15 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
        then
          (do
            let w__1700 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1700 <b 1887) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1701 : Bool)
      then
        (do
          writeReg SEE 1887
          let dtypeh := (BitVec.slice __opcode 23 2)
          let imm6 := (BitVec.slice __opcode 16 6)
          let dtypel := (BitVec.slice __opcode 13 2)
          let Pg := (BitVec.slice __opcode 10 3)
          let Rn := (BitVec.slice __opcode 5 5)
          let Zt := (BitVec.slice __opcode 0 5)
          (decode_LD1RSW_Z_P_BI_S64 dtypeh imm6 dtypel Pg Rn Zt)
          (pure false))
      else
        (do
          let w__1703 ← (( do
            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b1000010011#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
            then
              (do
                let w__1702 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1702 <b 1888) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1703 : Bool)
          then
            (do
              writeReg SEE 1888
              let dtypeh := (BitVec.slice __opcode 23 2)
              let imm6 := (BitVec.slice __opcode 16 6)
              let dtypel := (BitVec.slice __opcode 13 2)
              let Pg := (BitVec.slice __opcode 10 3)
              let Rn := (BitVec.slice __opcode 5 5)
              let Zt := (BitVec.slice __opcode 0 5)
              (decode_LD1RH_Z_P_BI_U16 dtypeh imm6 dtypel Pg Rn Zt)
              (pure false))
          else
            (do
              let w__1705 ← (( do
                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b1000010011#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 15 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                then
                  (do
                    let w__1704 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1704 <b 1889) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1705 : Bool)
              then
                (do
                  writeReg SEE 1889
                  let dtypeh := (BitVec.slice __opcode 23 2)
                  let imm6 := (BitVec.slice __opcode 16 6)
                  let dtypel := (BitVec.slice __opcode 13 2)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Zt := (BitVec.slice __opcode 0 5)
                  (decode_LD1RH_Z_P_BI_U32 dtypeh imm6 dtypel Pg Rn Zt)
                  (pure false))
              else
                (do
                  let w__1707 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b1000010011#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 15 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                    then
                      (do
                        let w__1706 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1706 <b 1890) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1707 : Bool)
                  then
                    (do
                      writeReg SEE 1890
                      let dtypeh := (BitVec.slice __opcode 23 2)
                      let imm6 := (BitVec.slice __opcode 16 6)
                      let dtypel := (BitVec.slice __opcode 13 2)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let Zt := (BitVec.slice __opcode 0 5)
                      (decode_LD1RH_Z_P_BI_U64 dtypeh imm6 dtypel Pg Rn Zt)
                      (pure false))
                  else
                    (do
                      let w__1709 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31
                                 22)) == (0b1000010101#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 15 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                        then
                          (do
                            let w__1708 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1708 <b 1891) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1709 : Bool)
                      then
                        (do
                          writeReg SEE 1891
                          let dtypeh := (BitVec.slice __opcode 23 2)
                          let imm6 := (BitVec.slice __opcode 16 6)
                          let dtypel := (BitVec.slice __opcode 13 2)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let Zt := (BitVec.slice __opcode 0 5)
                          (decode_LD1RSH_Z_P_BI_S64 dtypeh imm6 dtypel Pg Rn Zt)
                          (pure false))
                      else
                        (do
                          let w__1711 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode
                                     31 22)) == (0b1000010101#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                     __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                            then
                              (do
                                let w__1710 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1710 <b 1892) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1711 : Bool)
                          then
                            (do
                              writeReg SEE 1892
                              let dtypeh := (BitVec.slice __opcode 23 2)
                              let imm6 := (BitVec.slice __opcode 16 6)
                              let dtypel := (BitVec.slice __opcode 13 2)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let Zt := (BitVec.slice __opcode 0 5)
                              (decode_LD1RSH_Z_P_BI_S32 dtypeh imm6 dtypel Pg Rn Zt)
                              (pure false))
                          else
                            (do
                              let w__1713 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                         __opcode 31 22)) == (0b1000010101#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 15 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1712 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1712 <b 1893) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1713 : Bool)
                              then
                                (do
                                  writeReg SEE 1893
                                  let dtypeh := (BitVec.slice __opcode 23 2)
                                  let imm6 := (BitVec.slice __opcode 16 6)
                                  let dtypel := (BitVec.slice __opcode 13 2)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let Zt := (BitVec.slice __opcode 0 5)
                                  (decode_LD1RW_Z_P_BI_U32 dtypeh imm6 dtypel Pg Rn Zt)
                                  (pure false))
                              else
                                (do
                                  let w__1715 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                             __opcode 31 22)) == (0b1000010101#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 15 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1714 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1714 <b 1894) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1715 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1894
                                      let dtypeh := (BitVec.slice __opcode 23 2)
                                      let imm6 := (BitVec.slice __opcode 16 6)
                                      let dtypel := (BitVec.slice __opcode 13 2)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let Zt := (BitVec.slice __opcode 0 5)
                                      (decode_LD1RW_Z_P_BI_U64 dtypeh imm6 dtypel Pg Rn Zt)
                                      (pure false))
                                  else
                                    (do
                                      let w__1717 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                 __opcode 31 22)) == (0b1000010111#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 15 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1716 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1716 <b 1895) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1717 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1895
                                          let dtypeh := (BitVec.slice __opcode 23 2)
                                          let imm6 := (BitVec.slice __opcode 16 6)
                                          let dtypel := (BitVec.slice __opcode 13 2)
                                          let Pg := (BitVec.slice __opcode 10 3)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let Zt := (BitVec.slice __opcode 0 5)
                                          (decode_LD1RSB_Z_P_BI_S64 dtypeh imm6 dtypel Pg Rn Zt)
                                          (pure false))
                                      else
                                        (do
                                          let w__1719 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                     __opcode 31 22)) == (0b1000010111#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1718 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1718 <b 1896) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1719 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1896
                                              let dtypeh := (BitVec.slice __opcode 23 2)
                                              let imm6 := (BitVec.slice __opcode 16 6)
                                              let dtypel := (BitVec.slice __opcode 13 2)
                                              let Pg := (BitVec.slice __opcode 10 3)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let Zt := (BitVec.slice __opcode 0 5)
                                              (decode_LD1RSB_Z_P_BI_S32 dtypeh imm6 dtypel Pg Rn Zt)
                                              (pure false))
                                          else
                                            (do
                                              let w__1721 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                         __opcode 31 22)) == (0b1000010111#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 15 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1720 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1720 <b 1897) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1721 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1897
                                                  let dtypeh := (BitVec.slice __opcode 23 2)
                                                  let imm6 := (BitVec.slice __opcode 16 6)
                                                  let dtypel := (BitVec.slice __opcode 13 2)
                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                  (decode_LD1RSB_Z_P_BI_S16 dtypeh imm6 dtypel Pg Rn
                                                    Zt)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1723 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                             __opcode 31 22)) == (0b1000010111#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 15 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1722 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1722 <b 1898) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1723 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1898
                                                      let dtypeh := (BitVec.slice __opcode 23 2)
                                                      let imm6 := (BitVec.slice __opcode 16 6)
                                                      let dtypel := (BitVec.slice __opcode 13 2)
                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                      (decode_LD1RD_Z_P_BI_U64 dtypeh imm6 dtypel Pg
                                                        Rn Zt)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1725 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b10100100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 15 13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1724 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1724 <b 1899) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1725 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1899
                                                          let dtype := (BitVec.slice __opcode 21 4)
                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                          (decode_LD1B_Z_P_BR_U8 dtype Rm Pg Rn Zt)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1727 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b10100100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 15 13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1726 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1726 <b 1900) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1727 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1900
                                                              let dtype :=
                                                                (BitVec.slice __opcode 21 4)
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                              (decode_LD1B_Z_P_BR_U16 dtype Rm Pg Rn
                                                                Zt)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1729 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 31 21)) == (0b10100100010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                         __opcode 15 13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1728 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1728 <b 1901) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1729 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1901
                                                                  let dtype :=
                                                                    (BitVec.slice __opcode 21 4)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zt :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_LD1B_Z_P_BR_U32 dtype Rm
                                                                    Pg Rn Zt)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1731 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                             __opcode 31 21)) == (0b10100100011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                             __opcode 15 13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1730 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1730 <b 1902) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1731 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1902
                                                                      let dtype :=
                                                                        (BitVec.slice __opcode 21 4)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let Pg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zt :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_LD1B_Z_P_BR_U64 dtype
                                                                        Rm Pg Rn Zt)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1733 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 21)) == (0b10100100100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1732 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1732 <b 1903) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1733 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1903
                                                                          let dtype :=
                                                                            (BitVec.slice __opcode
                                                                              21 4)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let Pg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zt :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_LD1SW_Z_P_BR_S64
                                                                            dtype Rm Pg Rn Zt)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1735 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b10100100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1734 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1734 <b 1904) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1735 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1904
                                                                              let dtype :=
                                                                                (BitVec.slice
                                                                                  __opcode 21 4)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let Pg :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Zt :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_LD1H_Z_P_BR_U16
                                                                                dtype Rm Pg Rn Zt)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1737 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         21)) == (0b10100100110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1736 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1736 <b 1905) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1737 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1905
                                                                                  let dtype :=
                                                                                    (BitVec.slice
                                                                                      __opcode 21 4)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let Pg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Zt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_LD1H_Z_P_BR_U32
                                                                                    dtype Rm Pg Rn
                                                                                    Zt)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1739 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 21)) == (0b10100100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1738 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1738 <b 1906) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1739 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1906
                                                                                      let dtype :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          21 4)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let Pg :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Zt :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_LD1H_Z_P_BR_U64
                                                                                        dtype Rm Pg
                                                                                        Rn Zt)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1741 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 21)) == (0b10100101000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1740 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1740 <b 1907) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1741 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1907
                                                                                          let dtype :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              21 4)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let Pg :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 3)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Zt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_LD1SH_Z_P_BR_S64
                                                                                            dtype Rm
                                                                                            Pg Rn Zt)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1743 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     21)) == (0b10100101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1742 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1742 <b 1908) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1743 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1908
                                                                                              let dtype :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  21
                                                                                                  4)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  5)
                                                                                              let Pg :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  3)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let Zt :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              (decode_LD1SH_Z_P_BR_S32
                                                                                                dtype
                                                                                                Rm
                                                                                                Pg
                                                                                                Rn
                                                                                                Zt)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1745 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         21)) == (0b10100101010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1744 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1744 <b 1909) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1745 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1909
                                                                                                  let dtype :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      21
                                                                                                      4)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let Pg :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      3)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let Zt :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  (decode_LD1W_Z_P_BR_U32
                                                                                                    dtype
                                                                                                    Rm
                                                                                                    Pg
                                                                                                    Rn
                                                                                                    Zt)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1747 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             21)) == (0b10100101011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1746 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1746 <b 1910) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1747 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1910
                                                                                                      let dtype :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          21
                                                                                                          4)
                                                                                                      let Rm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          5)
                                                                                                      let Pg :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          3)
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let Zt :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      (decode_LD1W_Z_P_BR_U64
                                                                                                        dtype
                                                                                                        Rm
                                                                                                        Pg
                                                                                                        Rn
                                                                                                        Zt)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1749 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b10100101100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1748 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1748 <b 1911) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1749 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1911
                                                                                                          let dtype :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              21
                                                                                                              4)
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let Pg :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              3)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let Zt :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          (decode_LD1SB_Z_P_BR_S64
                                                                                                            dtype
                                                                                                            Rm
                                                                                                            Pg
                                                                                                            Rn
                                                                                                            Zt)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1751 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     21)) == (0b10100101101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1750 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1750 <b 1912) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1751 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1912
                                                                                                              let dtype :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  21
                                                                                                                  4)
                                                                                                              let Rm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
                                                                                                              let Pg :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  3)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let Zt :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              (decode_LD1SB_Z_P_BR_S32
                                                                                                                dtype
                                                                                                                Rm
                                                                                                                Pg
                                                                                                                Rn
                                                                                                                Zt)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1753 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         21)) == (0b10100101110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1752 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1752 <b 1913) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1753 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1913
                                                                                                                  let dtype :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      21
                                                                                                                      4)
                                                                                                                  let Rm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let Pg :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      3)
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let Zt :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  (decode_LD1SB_Z_P_BR_S16
                                                                                                                    dtype
                                                                                                                    Rm
                                                                                                                    Pg
                                                                                                                    Rn
                                                                                                                    Zt)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1755 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             21)) == (0b10100101111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             13)) == (0b010#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1754 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1754 <b 1914) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1755 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1914
                                                                                                                      let dtype :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          21
                                                                                                                          4)
                                                                                                                      let Rm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          5)
                                                                                                                      let Pg :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          3)
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let Zt :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      (decode_LD1D_Z_P_BR_U64
                                                                                                                        dtype
                                                                                                                        Rm
                                                                                                                        Pg
                                                                                                                        Rn
                                                                                                                        Zt)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1757 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b10100101000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 15
                                                                                                                                 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1756 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1756 <b 1915) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1757 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1915
                                                                                                                          let dtype :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              23
                                                                                                                              2)
                                                                                                                          let Rm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let Pg :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              3)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let Zt :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          (decode_LD1W_Z_P_BR_U128
                                                                                                                            dtype
                                                                                                                            Rm
                                                                                                                            Pg
                                                                                                                            Rn
                                                                                                                            Zt)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1759 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b10100101100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     15
                                                                                                                                     13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1758 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1758 <b 1916) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1759 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1916
                                                                                                                              let dtype :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  23
                                                                                                                                  2)
                                                                                                                              let Rm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  5)
                                                                                                                              let Pg :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  3)
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let Zt :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              (decode_LD1D_Z_P_BR_U128
                                                                                                                                dtype
                                                                                                                                Rm
                                                                                                                                Pg
                                                                                                                                Rn
                                                                                                                                Zt)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1761 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b10100100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         15
                                                                                                                                         13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1760 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1760 <b 1917) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1761 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1917
                                                                                                                                  let dtype :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      21
                                                                                                                                      4)
                                                                                                                                  let Rm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let Pg :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      3)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let Zt :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  (decode_LDFF1B_Z_P_BR_U8
                                                                                                                                    dtype
                                                                                                                                    Rm
                                                                                                                                    Pg
                                                                                                                                    Rn
                                                                                                                                    Zt)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1763 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b10100100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             15
                                                                                                                                             13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1762 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1762 <b 1918) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1763 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1918
                                                                                                                                      let dtype :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          21
                                                                                                                                          4)
                                                                                                                                      let Rm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      let Pg :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          3)
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let Zt :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      (decode_LDFF1B_Z_P_BR_U16
                                                                                                                                        dtype
                                                                                                                                        Rm
                                                                                                                                        Pg
                                                                                                                                        Rn
                                                                                                                                        Zt)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1765 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b10100100010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1764 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1764 <b 1919) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1765 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1919
                                                                                                                                          let dtype :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              21
                                                                                                                                              4)
                                                                                                                                          let Rm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              5)
                                                                                                                                          let Pg :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              10
                                                                                                                                              3)
                                                                                                                                          let Rn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let Zt :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_LDFF1B_Z_P_BR_U32
                                                                                                                                            dtype
                                                                                                                                            Rm
                                                                                                                                            Pg
                                                                                                                                            Rn
                                                                                                                                            Zt)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1767 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b10100100011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1766 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1766 <b 1920) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1767 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1920
                                                                                                                                              let dtype :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  21
                                                                                                                                                  4)
                                                                                                                                              let Rm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  5)
                                                                                                                                              let Pg :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  10
                                                                                                                                                  3)
                                                                                                                                              let Rn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let Zt :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              (decode_LDFF1B_Z_P_BR_U64
                                                                                                                                                dtype
                                                                                                                                                Rm
                                                                                                                                                Pg
                                                                                                                                                Rn
                                                                                                                                                Zt)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__1769 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         21)) == (0b10100100100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         15
                                                                                                                                                         13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__1768 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__1768 <b 1921) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__1769 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1921
                                                                                                                                                  let dtype :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      21
                                                                                                                                                      4)
                                                                                                                                                  let Rm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      5)
                                                                                                                                                  let Pg :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      10
                                                                                                                                                      3)
                                                                                                                                                  let Rn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let Zt :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_LDFF1SW_Z_P_BR_S64
                                                                                                                                                    dtype
                                                                                                                                                    Rm
                                                                                                                                                    Pg
                                                                                                                                                    Rn
                                                                                                                                                    Zt)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__1771 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             21)) == (0b10100100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__1770 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__1770 <b 1922) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__1771 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1922
                                                                                                                                                      let dtype :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          21
                                                                                                                                                          4)
                                                                                                                                                      let Rm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          5)
                                                                                                                                                      let Pg :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          10
                                                                                                                                                          3)
                                                                                                                                                      let Rn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let Zt :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_LDFF1H_Z_P_BR_U16
                                                                                                                                                        dtype
                                                                                                                                                        Rm
                                                                                                                                                        Pg
                                                                                                                                                        Rn
                                                                                                                                                        Zt)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__1773 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 21)) == (0b10100100110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 15
                                                                                                                                                                 13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__1772 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__1772 <b 1923) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__1773 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1923
                                                                                                                                                          let dtype :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              21
                                                                                                                                                              4)
                                                                                                                                                          let Rm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              5)
                                                                                                                                                          let Pg :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              3)
                                                                                                                                                          let Rn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              5)
                                                                                                                                                          let Zt :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          (decode_LDFF1H_Z_P_BR_U32
                                                                                                                                                            dtype
                                                                                                                                                            Rm
                                                                                                                                                            Pg
                                                                                                                                                            Rn
                                                                                                                                                            Zt)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__1775 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     21)) == (0b10100100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     15
                                                                                                                                                                     13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__1774 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__1774 <b 1924) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__1775 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 1924
                                                                                                                                                              let dtype :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  21
                                                                                                                                                                  4)
                                                                                                                                                              let Rm :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  5)
                                                                                                                                                              let Pg :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  10
                                                                                                                                                                  3)
                                                                                                                                                              let Rn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  5)
                                                                                                                                                              let Zt :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  5)
                                                                                                                                                              (decode_LDFF1H_Z_P_BR_U64
                                                                                                                                                                dtype
                                                                                                                                                                Rm
                                                                                                                                                                Pg
                                                                                                                                                                Rn
                                                                                                                                                                Zt)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__1777 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         21)) == (0b10100101000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         15
                                                                                                                                                                         13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__1776 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__1776 <b 1925) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__1777 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 1925
                                                                                                                                                                  let dtype :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      21
                                                                                                                                                                      4)
                                                                                                                                                                  let Rm :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      5)
                                                                                                                                                                  let Pg :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      10
                                                                                                                                                                      3)
                                                                                                                                                                  let Rn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      5
                                                                                                                                                                      5)
                                                                                                                                                                  let Zt :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      5)
                                                                                                                                                                  (decode_LDFF1SH_Z_P_BR_S64
                                                                                                                                                                    dtype
                                                                                                                                                                    Rm
                                                                                                                                                                    Pg
                                                                                                                                                                    Rn
                                                                                                                                                                    Zt)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__1779 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             21)) == (0b10100101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             15
                                                                                                                                                                             13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__1778 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__1778 <b 1926) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__1779 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 1926
                                                                                                                                                                      let dtype :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          21
                                                                                                                                                                          4)
                                                                                                                                                                      let Rm :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          16
                                                                                                                                                                          5)
                                                                                                                                                                      let Pg :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          10
                                                                                                                                                                          3)
                                                                                                                                                                      let Rn :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          5
                                                                                                                                                                          5)
                                                                                                                                                                      let Zt :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          0
                                                                                                                                                                          5)
                                                                                                                                                                      (decode_LDFF1SH_Z_P_BR_S32
                                                                                                                                                                        dtype
                                                                                                                                                                        Rm
                                                                                                                                                                        Pg
                                                                                                                                                                        Rn
                                                                                                                                                                        Zt)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__1781 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 21)) == (0b10100101010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 15
                                                                                                                                                                                 13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__1780 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__1780 <b 1927) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__1781 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 1927
                                                                                                                                                                          let dtype :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              21
                                                                                                                                                                              4)
                                                                                                                                                                          let Rm :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              5)
                                                                                                                                                                          let Pg :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              10
                                                                                                                                                                              3)
                                                                                                                                                                          let Rn :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              5
                                                                                                                                                                              5)
                                                                                                                                                                          let Zt :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              5)
                                                                                                                                                                          (decode_LDFF1W_Z_P_BR_U32
                                                                                                                                                                            dtype
                                                                                                                                                                            Rm
                                                                                                                                                                            Pg
                                                                                                                                                                            Rn
                                                                                                                                                                            Zt)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__1783 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     31
                                                                                                                                                                                     21)) == (0b10100101011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     15
                                                                                                                                                                                     13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__1782 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__1782 <b 1928) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__1783 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 1928
                                                                                                                                                                              let dtype :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  21
                                                                                                                                                                                  4)
                                                                                                                                                                              let Rm :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  16
                                                                                                                                                                                  5)
                                                                                                                                                                              let Pg :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  10
                                                                                                                                                                                  3)
                                                                                                                                                                              let Rn :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  5
                                                                                                                                                                                  5)
                                                                                                                                                                              let Zt :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  0
                                                                                                                                                                                  5)
                                                                                                                                                                              (decode_LDFF1W_Z_P_BR_U64
                                                                                                                                                                                dtype
                                                                                                                                                                                Rm
                                                                                                                                                                                Pg
                                                                                                                                                                                Rn
                                                                                                                                                                                Zt)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__1785 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         31
                                                                                                                                                                                         21)) == (0b10100101100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         15
                                                                                                                                                                                         13)) == (0b011#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__1784 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__1784 <b 1929) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__1785 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 1929
                                                                                                                                                                                  let dtype :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      21
                                                                                                                                                                                      4)
                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      16
                                                                                                                                                                                      5)
                                                                                                                                                                                  let Pg :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      10
                                                                                                                                                                                      3)
                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      5
                                                                                                                                                                                      5)
                                                                                                                                                                                  let Zt :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      0
                                                                                                                                                                                      5)
                                                                                                                                                                                  (decode_LDFF1SB_Z_P_BR_S64
                                                                                                                                                                                    dtype
                                                                                                                                                                                    Rm
                                                                                                                                                                                    Pg
                                                                                                                                                                                    Rn
                                                                                                                                                                                    Zt)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
