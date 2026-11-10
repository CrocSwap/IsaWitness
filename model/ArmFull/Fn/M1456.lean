import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0160
import ArmFull.Fn.M0161
import ArmFull.Fn.M0186
import ArmFull.Fn.M0261
import ArmFull.Fn.M0265
import ArmFull.Fn.M0269
import ArmFull.Fn.M0276
import ArmFull.Fn.M0277
import ArmFull.Fn.M0313
import ArmFull.Fn.M0314
import ArmFull.Fn.M0315
import ArmFull.Fn.M0321
import ArmFull.Fn.M0322
import ArmFull.Fn.M0323
import ArmFull.Fn.M0324
import ArmFull.Fn.M0325
import ArmFull.Fn.M0326
import ArmFull.Fn.M0327
import ArmFull.Fn.M0333
import ArmFull.Fn.M0334
import ArmFull.Fn.M0335
import ArmFull.Fn.M0336
import ArmFull.Fn.M0337
import ArmFull.Fn.M0338
import ArmFull.Fn.M0342
import ArmFull.Fn.M0343
import ArmFull.Fn.M0347
import ArmFull.Fn.M0349
import ArmFull.Fn.M0351
import ArmFull.Fn.M0354
import ArmFull.Fn.M0357
import ArmFull.Fn.M0392
import ArmFull.Fn.M0394
import ArmFull.Fn.M0397
import ArmFull.Fn.M0430
import ArmFull.Fn.M0432
import ArmFull.Fn.M1351
import ArmFull.Fn.M1361
import ArmFull.Fn.M1365
import ArmFull.Fn.M1366
import ArmFull.Fn.M1367
import ArmFull.Fn.M1373
import ArmFull.Fn.M1374
import ArmFull.Fn.M1375
import ArmFull.Fn.M1378

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

/-- Type quantifiers: t : Int -/
def AArch64_AutoGen_SysRegRead__seg6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Bool := do
  if ((((((CRm == 0b0001#4) && (CRn == 0b0011#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
  then
    (do
      (HDFGWTR_EL2_SysRegRead_c6796c2a296d66f8 el op0 op1 CRn op2 CRm t)
      (pure false))
  else
    (do
      if ((((((CRm == 0b0011#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
      then
        (do
          (APGAKeyLo_EL1_SysRegRead_b90c447e3bdb3387 el op0 op1 CRn op2 CRm t)
          (pure false))
      else
        (do
          if ((((((CRm == 0b0010#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
          then
            (do
              (APDAKeyHi_EL1_SysRegRead_6f8bf97afb0e465f el op0 op1 CRn op2 CRm t)
              (pure false))
          else
            (do
              if ((((((CRm == 0b1100#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
              then
                (do
                  (PMCEID1_EL0_SysRegRead_88fe472f132d5d45 el op0 op1 CRn op2 CRm t)
                  (pure false))
              else
                (do
                  if ((((((CRm == 0b0010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b111#3)) && (op2 == 0b010#3)) : Bool)
                  then
                    (do
                      (CNTPS_CVAL_EL1_SysRegRead_21e9c10a0f76a1d1 el op0 op1 CRn op2 CRm t)
                      (pure false))
                  else
                    (do
                      if ((((((CRm == 0b0010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b111#3)) && (op2 == 0b000#3)) : Bool)
                      then
                        (do
                          (CNTPS_TVAL_EL1_SysRegRead_748a1753bd033377 el op0 op1 CRn op2 CRm t)
                          (pure false))
                      else
                        (do
                          if ((((((CRm == 0b0101#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                          then
                            (do
                              (ID_AA64AFR1_EL1_SysRegRead_1072eb4f153853b5 el op0 op1 CRn op2 CRm t)
                              (pure false))
                          else
                            (do
                              if ((((((CRm == 0b0001#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b001#3)) : Bool)
                              then
                                (do
                                  (MAIR2_EL3_SysRegRead_06e8ce86a19999af el op0 op1 CRn op2 CRm t)
                                  (pure false))
                              else
                                (do
                                  if ((((((CRm == 0b0100#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                  then
                                    (do
                                      (LOREA_EL1_SysRegRead_c69af0a70feec9d7 el op0 op1 CRn op2 CRm
                                        t)
                                      (pure false))
                                  else
                                    (do
                                      if ((((((CRm == 0b0011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                                      then
                                        (do
                                          (CNTV_TVAL_EL0_SysRegRead_f682815b8c52312a el op0 op1 CRn
                                            op2 CRm t)
                                          (pure false))
                                      else
                                        (do
                                          if ((((((CRm == 0b0010#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                          then
                                            (do
                                              (APDBKeyLo_EL1_SysRegRead_d57fe909b886c0fe el op0 op1
                                                CRn op2 CRm t)
                                              (pure false))
                                          else
                                            (do
                                              if ((((((CRm == 0b1101#4) && (CRn == 0b1001#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                              then
                                                (do
                                                  (SPMDEVARCH_EL1_SysRegRead_f379f5d64ab8b025 el op0
                                                    op1 CRn op2 CRm t)
                                                  (pure false))
                                              else
                                                (do
                                                  if ((((((CRm == 0b1001#4) && (CRn == 0b0111#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                  then
                                                    (do
                                                      (DBGCLAIMCLR_EL1_SysRegRead_ffbb497475eb383a
                                                        el op0 op1 CRn op2 CRm t)
                                                      (pure false))
                                                  else
                                                    (do
                                                      if ((((((CRm == 0b1111#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                      then
                                                        (do
                                                          (DBGBVR_EL1_SysRegRead_d8b7590f7c00d19c el
                                                            op0 op1 CRn op2 CRm t)
                                                          (pure false))
                                                      else
                                                        (do
                                                          if ((((((CRm == 0b1110#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                          then
                                                            (do
                                                              (DBGBVR_EL1_SysRegRead_c3ec1516735db5f7
                                                                el op0 op1 CRn op2 CRm t)
                                                              (pure false))
                                                          else
                                                            (do
                                                              if ((((((CRm == 0b1101#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                              then
                                                                (do
                                                                  (DBGBVR_EL1_SysRegRead_d4c2dcc933af38a7
                                                                    el op0 op1 CRn op2 CRm t)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  if ((((((CRm == 0b1100#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                  then
                                                                    (do
                                                                      (DBGBVR_EL1_SysRegRead_8a3cda8f4660427a
                                                                        el op0 op1 CRn op2 CRm t)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      if ((((((CRm == 0b1011#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                      then
                                                                        (do
                                                                          (DBGBVR_EL1_SysRegRead_351ab37f466f6889
                                                                            el op0 op1 CRn op2 CRm t)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          if ((((((CRm == 0b1010#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                          then
                                                                            (do
                                                                              (DBGBVR_EL1_SysRegRead_8c3e53570d26ce7a
                                                                                el op0 op1 CRn op2
                                                                                CRm t)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              if ((((((CRm == 0b1001#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                              then
                                                                                (do
                                                                                  (DBGBVR_EL1_SysRegRead_ab88cca85ec0eca9
                                                                                    el op0 op1 CRn
                                                                                    op2 CRm t)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  if ((((((CRm == 0b1000#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      (DBGBVR_EL1_SysRegRead_a18f410293f246c4
                                                                                        el op0 op1
                                                                                        CRn op2 CRm
                                                                                        t)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      if ((((((CRm == 0b0111#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          (DBGBVR_EL1_SysRegRead_755afa7df870d9ab
                                                                                            el op0
                                                                                            op1 CRn
                                                                                            op2 CRm
                                                                                            t)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              (DBGBVR_EL1_SysRegRead_c5088163afaa4276
                                                                                                el
                                                                                                op0
                                                                                                op1
                                                                                                CRn
                                                                                                op2
                                                                                                CRm
                                                                                                t)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              if ((((((CRm == 0b0101#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  (DBGBVR_EL1_SysRegRead_25b8861425ee4c26
                                                                                                    el
                                                                                                    op0
                                                                                                    op1
                                                                                                    CRn
                                                                                                    op2
                                                                                                    CRm
                                                                                                    t)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  if ((((((CRm == 0b0100#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      (DBGBVR_EL1_SysRegRead_9deb23233bdb8631
                                                                                                        el
                                                                                                        op0
                                                                                                        op1
                                                                                                        CRn
                                                                                                        op2
                                                                                                        CRm
                                                                                                        t)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((((((CRm == 0b0011#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          (DBGBVR_EL1_SysRegRead_a6904466fe9c7a54
                                                                                                            el
                                                                                                            op0
                                                                                                            op1
                                                                                                            CRn
                                                                                                            op2
                                                                                                            CRm
                                                                                                            t)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              (DBGBVR_EL1_SysRegRead_7e4c0d4f3367d780
                                                                                                                el
                                                                                                                op0
                                                                                                                op1
                                                                                                                CRn
                                                                                                                op2
                                                                                                                CRm
                                                                                                                t)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((((((CRm == 0b0001#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  (DBGBVR_EL1_SysRegRead_08fe9aa719e4e44c
                                                                                                                    el
                                                                                                                    op0
                                                                                                                    op1
                                                                                                                    CRn
                                                                                                                    op2
                                                                                                                    CRm
                                                                                                                    t)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      (DBGBVR_EL1_SysRegRead_5ed77d081c253be3
                                                                                                                        el
                                                                                                                        op0
                                                                                                                        op1
                                                                                                                        CRn
                                                                                                                        op2
                                                                                                                        CRm
                                                                                                                        t)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((((((CRm == 0b1100#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          (PMCEID0_EL0_SysRegRead_f2e86782f8f3f9b7
                                                                                                                            el
                                                                                                                            op0
                                                                                                                            op1
                                                                                                                            CRn
                                                                                                                            op2
                                                                                                                            CRm
                                                                                                                            t)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((((((CRm == 0b1111#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              (DBGWVR_EL1_SysRegRead_419765ae001a7669
                                                                                                                                el
                                                                                                                                op0
                                                                                                                                op1
                                                                                                                                CRn
                                                                                                                                op2
                                                                                                                                CRm
                                                                                                                                t)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((((((CRm == 0b1110#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  (DBGWVR_EL1_SysRegRead_27540f902a0177f1
                                                                                                                                    el
                                                                                                                                    op0
                                                                                                                                    op1
                                                                                                                                    CRn
                                                                                                                                    op2
                                                                                                                                    CRm
                                                                                                                                    t)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((((((CRm == 0b1101#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      (DBGWVR_EL1_SysRegRead_3ea4dd4eabbc6db1
                                                                                                                                        el
                                                                                                                                        op0
                                                                                                                                        op1
                                                                                                                                        CRn
                                                                                                                                        op2
                                                                                                                                        CRm
                                                                                                                                        t)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((((((CRm == 0b1100#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          (DBGWVR_EL1_SysRegRead_3ad260c7658f264f
                                                                                                                                            el
                                                                                                                                            op0
                                                                                                                                            op1
                                                                                                                                            CRn
                                                                                                                                            op2
                                                                                                                                            CRm
                                                                                                                                            t)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((((((CRm == 0b1011#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              (DBGWVR_EL1_SysRegRead_6c69a5a56e08fe81
                                                                                                                                                el
                                                                                                                                                op0
                                                                                                                                                op1
                                                                                                                                                CRn
                                                                                                                                                op2
                                                                                                                                                CRm
                                                                                                                                                t)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((((((CRm == 0b1010#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  (DBGWVR_EL1_SysRegRead_bfffa222b59a2eac
                                                                                                                                                    el
                                                                                                                                                    op0
                                                                                                                                                    op1
                                                                                                                                                    CRn
                                                                                                                                                    op2
                                                                                                                                                    CRm
                                                                                                                                                    t)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if ((((((CRm == 0b1001#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      (DBGWVR_EL1_SysRegRead_395e92ea6cb1cbd3
                                                                                                                                                        el
                                                                                                                                                        op0
                                                                                                                                                        op1
                                                                                                                                                        CRn
                                                                                                                                                        op2
                                                                                                                                                        CRm
                                                                                                                                                        t)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if ((((((CRm == 0b1000#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          (DBGWVR_EL1_SysRegRead_e481fcd4bbdbbbdd
                                                                                                                                                            el
                                                                                                                                                            op0
                                                                                                                                                            op1
                                                                                                                                                            CRn
                                                                                                                                                            op2
                                                                                                                                                            CRm
                                                                                                                                                            t)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if ((((((CRm == 0b0111#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              (DBGWVR_EL1_SysRegRead_fae261a7c3341309
                                                                                                                                                                el
                                                                                                                                                                op0
                                                                                                                                                                op1
                                                                                                                                                                CRn
                                                                                                                                                                op2
                                                                                                                                                                CRm
                                                                                                                                                                t)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  (DBGWVR_EL1_SysRegRead_469f2550ef085d68
                                                                                                                                                                    el
                                                                                                                                                                    op0
                                                                                                                                                                    op1
                                                                                                                                                                    CRn
                                                                                                                                                                    op2
                                                                                                                                                                    CRm
                                                                                                                                                                    t)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((((((CRm == 0b0101#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      (DBGWVR_EL1_SysRegRead_5cfc3b8e8ae8a2a4
                                                                                                                                                                        el
                                                                                                                                                                        op0
                                                                                                                                                                        op1
                                                                                                                                                                        CRn
                                                                                                                                                                        op2
                                                                                                                                                                        CRm
                                                                                                                                                                        t)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((((((CRm == 0b0100#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          (DBGWVR_EL1_SysRegRead_dd3a55e2d9bbec8f
                                                                                                                                                                            el
                                                                                                                                                                            op0
                                                                                                                                                                            op1
                                                                                                                                                                            CRn
                                                                                                                                                                            op2
                                                                                                                                                                            CRm
                                                                                                                                                                            t)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((((((CRm == 0b0011#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              (DBGWVR_EL1_SysRegRead_9cebffd3d1c8ceeb
                                                                                                                                                                                el
                                                                                                                                                                                op0
                                                                                                                                                                                op1
                                                                                                                                                                                CRn
                                                                                                                                                                                op2
                                                                                                                                                                                CRm
                                                                                                                                                                                t)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  (DBGWVR_EL1_SysRegRead_06f47f0db897fdec
                                                                                                                                                                                    el
                                                                                                                                                                                    op0
                                                                                                                                                                                    op1
                                                                                                                                                                                    CRn
                                                                                                                                                                                    op2
                                                                                                                                                                                    CRm
                                                                                                                                                                                    t)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      (DBGWVR_EL1_SysRegRead_695a90ac9c89a050
                                                                                                                                                                                        el
                                                                                                                                                                                        op0
                                                                                                                                                                                        op1
                                                                                                                                                                                        CRn
                                                                                                                                                                                        op2
                                                                                                                                                                                        CRm
                                                                                                                                                                                        t)
                                                                                                                                                                                      (pure false))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          (DBGWVR_EL1_SysRegRead_19cc269e021d29f0
                                                                                                                                                                                            el
                                                                                                                                                                                            op0
                                                                                                                                                                                            op1
                                                                                                                                                                                            CRn
                                                                                                                                                                                            op2
                                                                                                                                                                                            CRm
                                                                                                                                                                                            t)
                                                                                                                                                                                          (pure false))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              (PIRE0_EL1_SysRegRead_1431908c1f187dd9
                                                                                                                                                                                                el
                                                                                                                                                                                                op0
                                                                                                                                                                                                op1
                                                                                                                                                                                                CRn
                                                                                                                                                                                                op2
                                                                                                                                                                                                CRm
                                                                                                                                                                                                t)
                                                                                                                                                                                              (pure false))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((((((CRm == 0b0101#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  (ID_AA64AFR0_EL1_SysRegRead_d690252709f00b61
                                                                                                                                                                                                    el
                                                                                                                                                                                                    op0
                                                                                                                                                                                                    op1
                                                                                                                                                                                                    CRn
                                                                                                                                                                                                    op2
                                                                                                                                                                                                    CRm
                                                                                                                                                                                                    t)
                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((((((CRm == 0b0001#4) && (CRn == 0b0101#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      (AFSR0_EL2_SysRegRead_acffc015481d1ac8
                                                                                                                                                                                                        el
                                                                                                                                                                                                        op0
                                                                                                                                                                                                        op1
                                                                                                                                                                                                        CRn
                                                                                                                                                                                                        op2
                                                                                                                                                                                                        CRm
                                                                                                                                                                                                        t)
                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((((((CRm == 0b0011#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          (AMAIR2_EL1_SysRegRead_961066b22ab5b10e
                                                                                                                                                                                                            el
                                                                                                                                                                                                            op0
                                                                                                                                                                                                            op1
                                                                                                                                                                                                            CRn
                                                                                                                                                                                                            op2
                                                                                                                                                                                                            CRm
                                                                                                                                                                                                            t)
                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((((((CRm == 0b0011#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              (ID_PFR2_EL1_SysRegRead_d9584bfc0ea04005
                                                                                                                                                                                                                el
                                                                                                                                                                                                                op0
                                                                                                                                                                                                                op1
                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                op2
                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                t)
                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  (CurrentEL_SysRegRead_94be544516d41cc8
                                                                                                                                                                                                                    el
                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((((((CRm == 0b1101#4) && (CRn == 0b1001#4)) && (op0 == 0b10#2)) && (op1 == 0b110#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      (SPMACCESSR_EL3_SysRegRead_04a853a73f22109c
                                                                                                                                                                                                                        el
                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((((((CRm == 0b0011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          (CNTHV_CTL_EL2_SysRegRead_fe7c25cca2e88b3f
                                                                                                                                                                                                                            el
                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              (CNTVCT_EL0_SysRegRead_1d562372e622baf9
                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((((((CRm == 0b0100#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  (ID_AA64ZFR0_EL1_SysRegRead_dd573310e3efc3be
                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      (ZCR_EL3_SysRegRead_db53f2dcbaed5b3a
                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((((((CRm == 0b0010#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          (ZCR_EL1_SysRegRead_f79acfc1d948e192
                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              (ZCR_EL1_SysRegRead_ae33ffd6ee977eba
                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  (ZCR_EL2_SysRegRead_e12f14b3f5451ee5
                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      (SMCR_EL3_SysRegRead_131f4d5255bb9624
                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if ((((((CRm == 0b0010#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          (SMCR_EL1_SysRegRead_924df8670c1f630f
                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              (SMCR_EL1_SysRegRead_ea88aa9e02fbf3b4
                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  (SMCR_EL2_SysRegRead_c0f6766b3afb8b13
                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0100#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      (ID_AA64SMFR0_EL1_SysRegRead_8f4054d57f9da064
                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          (MPAMVPM2_EL2_SysRegRead_cd39f13f6feef099
                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              (MPAMVPM6_EL2_SysRegRead_a456f2178fffbd2a
                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  (MPAMVPM5_EL2_SysRegRead_b3b860d951143744
                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0100#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      (MPAMHCR_EL2_SysRegRead_29e51a9bb9c934dc
                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0100#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          (MPAMIDR_EL1_SysRegRead_e782b807b20cd739
                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              (MPAMVPM7_EL2_SysRegRead_7f9fcda98e26326e
                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0101#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  (MPAM2_EL2_SysRegRead_f89d395320b0f023
                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0101#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      (MPAM2_EL2_SysRegRead_8458d45c0c29ff85
                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          (MPAMVPM1_EL2_SysRegRead_d5133d205dd80497
                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              (MPAMVPM0_EL2_SysRegRead_0960f12de90321b6
                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  (MPAMVPM3_EL2_SysRegRead_3655c8ba5ed54616
                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0101#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      (MPAM3_EL3_SysRegRead_2770962b9f8f46c1
                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0101#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          (MPAM0_EL1_SysRegRead_26602bb382f28735
                                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0101#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              (MPAMSM_EL1_SysRegRead_8b218aacc540b1cb
                                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  (MPAMVPM4_EL2_SysRegRead_2c47261ee8f811ec
                                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0101#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      (MPAM1_EL1_SysRegRead_85039c69dab4c388
                                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0100#4) && (CRn == 0b1010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          (MPAMVPMV_EL2_SysRegRead_3717c7fd58152b67
                                                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b0000#4)) && (op0 == 0b11#2)) && (op1 == 0b001#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              (GMID_EL1_SysRegRead_df65333e6c977d08
                                                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b0101#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  (TFSR_EL3_SysRegRead_8cd0ca2e5d9daf2c
                                                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0110#4) && (CRn == 0b0101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      (TFSRE0_EL1_SysRegRead_e7166fad237839bf
                                                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b0101#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          (TFSR_EL2_SysRegRead_c301d170f18e0e34
                                                                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b0101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              (TFSR_EL2_SysRegRead_5ac7c240abc0c535
                                                                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b0101#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  (TFSR_EL1_SysRegRead_629d1d7950939eef
                                                                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      (RGSR_EL1_SysRegRead_64fa1a7b4e06fd7e
                                                                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          (GCR_EL1_SysRegRead_62bd5315db9a2829
                                                                                                                                                                                                                                                                                                                                                                            el
                                                                                                                                                                                                                                                                                                                                                                            op0
                                                                                                                                                                                                                                                                                                                                                                            op1
                                                                                                                                                                                                                                                                                                                                                                            CRn
                                                                                                                                                                                                                                                                                                                                                                            op2
                                                                                                                                                                                                                                                                                                                                                                            CRm
                                                                                                                                                                                                                                                                                                                                                                            t)
                                                                                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0010#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              (TCO_SysRegRead_fec6636824256193
                                                                                                                                                                                                                                                                                                                                                                                el
                                                                                                                                                                                                                                                                                                                                                                                op0
                                                                                                                                                                                                                                                                                                                                                                                op1
                                                                                                                                                                                                                                                                                                                                                                                CRn
                                                                                                                                                                                                                                                                                                                                                                                op2
                                                                                                                                                                                                                                                                                                                                                                                CRm
                                                                                                                                                                                                                                                                                                                                                                                t)
                                                                                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b1101#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  (AMEVCNTR1_EL0_SysRegRead_270554ed1cad7329
                                                                                                                                                                                                                                                                                                                                                                                    el
                                                                                                                                                                                                                                                                                                                                                                                    op0
                                                                                                                                                                                                                                                                                                                                                                                    op1
                                                                                                                                                                                                                                                                                                                                                                                    CRn
                                                                                                                                                                                                                                                                                                                                                                                    op2
                                                                                                                                                                                                                                                                                                                                                                                    CRm
                                                                                                                                                                                                                                                                                                                                                                                    t)
                                                                                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b1101#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                      (AMEVCNTR1_EL0_SysRegRead_c7849b6a9ce28268
                                                                                                                                                                                                                                                                                                                                                                                        el
                                                                                                                                                                                                                                                                                                                                                                                        op0
                                                                                                                                                                                                                                                                                                                                                                                        op1
                                                                                                                                                                                                                                                                                                                                                                                        CRn
                                                                                                                                                                                                                                                                                                                                                                                        op2
                                                                                                                                                                                                                                                                                                                                                                                        CRm
                                                                                                                                                                                                                                                                                                                                                                                        t)
                                                                                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
