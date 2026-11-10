import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0142
import ArmFull.Fn.M0162
import ArmFull.Fn.M0163
import ArmFull.Fn.M0164
import ArmFull.Fn.M0214
import ArmFull.Fn.M0437
import ArmFull.Fn.M0439
import ArmFull.Fn.M0440
import ArmFull.Fn.M0441
import ArmFull.Fn.M0442
import ArmFull.Fn.M0443
import ArmFull.Fn.M0444
import ArmFull.Fn.M0450
import ArmFull.Fn.M0467
import ArmFull.Fn.M0469
import ArmFull.Fn.M0474
import ArmFull.Fn.M0477
import ArmFull.Fn.M0478
import ArmFull.Fn.M0480
import ArmFull.Fn.M0481
import ArmFull.Fn.M0482
import ArmFull.Fn.M0483
import ArmFull.Fn.M0484
import ArmFull.Fn.M0485
import ArmFull.Fn.M0486
import ArmFull.Fn.M0498
import ArmFull.Fn.M0499
import ArmFull.Fn.M0500
import ArmFull.Fn.M0503
import ArmFull.Fn.M0514
import ArmFull.Fn.M0515
import ArmFull.Fn.M0516
import ArmFull.Fn.M0517
import ArmFull.Fn.M0518
import ArmFull.Fn.M0519
import ArmFull.Fn.M0520
import ArmFull.Fn.M0521
import ArmFull.Fn.M0522
import ArmFull.Fn.M0523
import ArmFull.Fn.M0524
import ArmFull.Fn.M0525
import ArmFull.Fn.M0526
import ArmFull.Fn.M0527
import ArmFull.Fn.M0540
import ArmFull.Fn.M1378
import ArmFull.Fn.M1385
import ArmFull.Fn.M1386
import ArmFull.Fn.M1390
import ArmFull.Fn.M1405

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
def AArch64_AutoGen_SysRegWrite__seg1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Bool := do
  if ((((((CRm == 0b0001#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b100#3)) : Bool)
  then
    (do
      (GPTBR_EL3_SysRegWrite_6f7a8066a1cb6176 el op0 op1 CRn op2 CRm t)
      (pure false))
  else
    (do
      if ((((((CRm == 0b0101#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
      then
        (do
          (SPMEVFILTR_EL0_SysRegWrite_6ac937d3ce7c080c el op0 op1 CRn op2 CRm t)
          (pure false))
      else
        (do
          if ((((((CRm == 0b0101#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
          then
            (do
              (SPMEVFILTR_EL0_SysRegWrite_63ddc3864e8582ee el op0 op1 CRn op2 CRm t)
              (pure false))
          else
            (do
              if ((((((CRm == 0b0101#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
              then
                (do
                  (SPMEVFILTR_EL0_SysRegWrite_20aefd1cb9d1a5ad el op0 op1 CRn op2 CRm t)
                  (pure false))
              else
                (do
                  if ((((((CRm == 0b0101#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                  then
                    (do
                      (SPMEVFILTR_EL0_SysRegWrite_d5a6ac5fd18a3308 el op0 op1 CRn op2 CRm t)
                      (pure false))
                  else
                    (do
                      if ((((((CRm == 0b0101#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                      then
                        (do
                          (SPMEVFILTR_EL0_SysRegWrite_88a821bdd88ae64a el op0 op1 CRn op2 CRm t)
                          (pure false))
                      else
                        (do
                          if ((((((CRm == 0b0101#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                          then
                            (do
                              (SPMEVFILTR_EL0_SysRegWrite_299c129e3abe1407 el op0 op1 CRn op2 CRm t)
                              (pure false))
                          else
                            (do
                              if ((((((CRm == 0b0101#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                              then
                                (do
                                  (SPMEVFILTR_EL0_SysRegWrite_c7152a5fedd83db1 el op0 op1 CRn op2
                                    CRm t)
                                  (pure false))
                              else
                                (do
                                  if ((((((CRm == 0b0101#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                  then
                                    (do
                                      (SPMEVFILTR_EL0_SysRegWrite_f1320088845e7cb6 el op0 op1 CRn
                                        op2 CRm t)
                                      (pure false))
                                  else
                                    (do
                                      if ((((((CRm == 0b0100#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                      then
                                        (do
                                          (SPMEVFILTR_EL0_SysRegWrite_437d4622cabaa331 el op0 op1
                                            CRn op2 CRm t)
                                          (pure false))
                                      else
                                        (do
                                          if ((((((CRm == 0b0100#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                          then
                                            (do
                                              (SPMEVFILTR_EL0_SysRegWrite_7801b81c1b7fe92f el op0
                                                op1 CRn op2 CRm t)
                                              (pure false))
                                          else
                                            (do
                                              if ((((((CRm == 0b0100#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                              then
                                                (do
                                                  (SPMEVFILTR_EL0_SysRegWrite_c6614df2d5b55f51 el
                                                    op0 op1 CRn op2 CRm t)
                                                  (pure false))
                                              else
                                                (do
                                                  if ((((((CRm == 0b0100#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                  then
                                                    (do
                                                      (SPMEVFILTR_EL0_SysRegWrite_ecb12bf267c7f798
                                                        el op0 op1 CRn op2 CRm t)
                                                      (pure false))
                                                  else
                                                    (do
                                                      if ((((((CRm == 0b0100#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                      then
                                                        (do
                                                          (SPMEVFILTR_EL0_SysRegWrite_182705557e8ea81d
                                                            el op0 op1 CRn op2 CRm t)
                                                          (pure false))
                                                      else
                                                        (do
                                                          if ((((((CRm == 0b0100#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                          then
                                                            (do
                                                              (SPMEVFILTR_EL0_SysRegWrite_800cff4b7bbd47cd
                                                                el op0 op1 CRn op2 CRm t)
                                                              (pure false))
                                                          else
                                                            (do
                                                              if ((((((CRm == 0b0100#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                              then
                                                                (do
                                                                  (SPMEVFILTR_EL0_SysRegWrite_34f238c7595c6e75
                                                                    el op0 op1 CRn op2 CRm t)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  if ((((((CRm == 0b0100#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                  then
                                                                    (do
                                                                      (SPMEVFILTR_EL0_SysRegWrite_e6a6baf23bbccd94
                                                                        el op0 op1 CRn op2 CRm t)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      if ((((((CRm == 0b0011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                      then
                                                                        (do
                                                                          (CNTHV_CVAL_EL2_SysRegWrite_a0eabf75b26da37c
                                                                            el op0 op1 CRn op2 CRm t)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          if ((((((CRm == 0b0011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                          then
                                                                            (do
                                                                              (CNTHV_CVAL_EL2_SysRegWrite_16bd78456d53d9ab
                                                                                el op0 op1 CRn op2
                                                                                CRm t)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b110#3)) && (op2 == 0b000#3)) : Bool)
                                                                              then
                                                                                (do
                                                                                  (TTBR0_EL3_SysRegWrite_3f52a3edf2b13467
                                                                                    el op0 op1 CRn
                                                                                    op2 CRm t)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  if ((((((CRm == 0b1111#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      (DBGBCR_EL1_SysRegWrite_2d22fdf5e1f2ca10
                                                                                        el op0 op1
                                                                                        CRn op2 CRm
                                                                                        t)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      if ((((((CRm == 0b1110#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          (DBGBCR_EL1_SysRegWrite_ffc42f78aa082453
                                                                                            el op0
                                                                                            op1 CRn
                                                                                            op2 CRm
                                                                                            t)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          if ((((((CRm == 0b1101#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              (DBGBCR_EL1_SysRegWrite_5aacf61e65fbc833
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
                                                                                              if ((((((CRm == 0b1100#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  (DBGBCR_EL1_SysRegWrite_ffdc1fc8f6c7fc45
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
                                                                                                  if ((((((CRm == 0b1011#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      (DBGBCR_EL1_SysRegWrite_61c83a14b45e16e7
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
                                                                                                      if ((((((CRm == 0b1010#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          (DBGBCR_EL1_SysRegWrite_35bdee83adebd0e9
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
                                                                                                          if ((((((CRm == 0b1001#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              (DBGBCR_EL1_SysRegWrite_88fc06956ff9a27d
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
                                                                                                              if ((((((CRm == 0b1000#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  (DBGBCR_EL1_SysRegWrite_5dfc64a898404c6e
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
                                                                                                                  if ((((((CRm == 0b0111#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      (DBGBCR_EL1_SysRegWrite_8f8afc10abdec5e5
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
                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          (DBGBCR_EL1_SysRegWrite_02aee1e0e30b8f1d
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
                                                                                                                          if ((((((CRm == 0b0101#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              (DBGBCR_EL1_SysRegWrite_061098b9cf5c8fa1
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
                                                                                                                              if ((((((CRm == 0b0100#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  (DBGBCR_EL1_SysRegWrite_ff386e82c1b05d03
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
                                                                                                                                  if ((((((CRm == 0b0011#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      (DBGBCR_EL1_SysRegWrite_744b1c8f0dd2fb3d
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
                                                                                                                                      if ((((((CRm == 0b0010#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          (DBGBCR_EL1_SysRegWrite_ded364def59ffa88
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
                                                                                                                                          if ((((((CRm == 0b0001#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              (DBGBCR_EL1_SysRegWrite_1e501456d6155d4d
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
                                                                                                                                              if ((((((CRm == 0b0000#4) && (CRn == 0b0000#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  (DBGBCR_EL1_SysRegWrite_6dec972069cd8973
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
                                                                                                                                                  if ((((((CRm == 0b1111#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      (PMCCFILTR_EL0_SysRegWrite_458a865c1359047a
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
                                                                                                                                                      if ((((((CRm == 0b1000#4) && (CRn == 0b0111#4)) && (op0 == 0b10#2)) && (op1 == 0b000#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          (DBGCLAIMSET_EL1_SysRegWrite_ebe44f0b96496255
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
                                                                                                                                                          if ((((((CRm == 0b1100#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              (ICC_SRE_EL1_SysRegWrite_b4fd95205f21b2e7
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
                                                                                                                                                              if ((((((CRm == 0b0011#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  (PM_SysRegWrite_b080c52627d6ad22
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
                                                                                                                                                                  if ((((((CRm == 0b1000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      (ICH_AP0R_EL2_SysRegWrite_ed1ffcaf90ab8639
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
                                                                                                                                                                      if ((((((CRm == 0b1000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          (ICH_AP0R_EL2_SysRegWrite_be89bf34888417e0
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
                                                                                                                                                                          if ((((((CRm == 0b1000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              (ICH_AP0R_EL2_SysRegWrite_1b21d2434fab897a
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
                                                                                                                                                                              if ((((((CRm == 0b1000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  (ICH_AP0R_EL2_SysRegWrite_78fe7c56d4742066
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
                                                                                                                                                                                  if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      (CONTEXTIDR_EL1_SysRegWrite_dd8dc6c6937913e2
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
                                                                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b1101#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          (TPIDR_EL1_SysRegWrite_be51f1ab4eeaabd3
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
                                                                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              (CNTVOFF_EL2_SysRegWrite_926108484bd738bb
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
                                                                                                                                                                                              if ((((((CRm == 0b1110#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  (PMUACR_EL1_SysRegWrite_5979643cbbbcd74b
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
                                                                                                                                                                                                  if ((((((CRm == 0b0101#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      (DSPSR_EL0_SysRegWrite_2829d14e4c67df55
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
                                                                                                                                                                                                      if ((((((CRm == 0b0000#4) && (CRn == 0b0001#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          (ACTLR_EL1_SysRegWrite_7b28af04d67b98b9
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
                                                                                                                                                                                                          if ((((((CRm == 0b0000#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              (RMR_EL2_SysRegWrite_fb0b01388c042301
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
                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b0010#4)) && (op0 == 0b11#2)) && (op1 == 0b100#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  (VNCR_EL2_SysRegWrite_4acc113d8c83cbf3
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
                                                                                                                                                                                                                  if ((((((CRm == 0b1110#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      (PMINTENCLR_EL1_SysRegWrite_8264587bba34a8f7
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
                                                                                                                                                                                                                      if ((((((CRm == 0b1100#4) && (CRn == 0b1001#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          (PMSELR_EL0_SysRegWrite_e127f02e29e8e39d
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
                                                                                                                                                                                                                          if ((((((CRm == 0b1100#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              (ICC_CTLR_EL1_SysRegWrite_6b2222909cfe4181
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
                                                                                                                                                                                                                              if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  (SPMEVFILT2R_EL0_SysRegWrite_69501ae43204dc12
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
                                                                                                                                                                                                                                  if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      (SPMEVFILT2R_EL0_SysRegWrite_a4da6c90289f656a
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
                                                                                                                                                                                                                                      if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          (SPMEVFILT2R_EL0_SysRegWrite_229ceb05708f41b3
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
                                                                                                                                                                                                                                          if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              (SPMEVFILT2R_EL0_SysRegWrite_15fbb8b13e7509b3
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
                                                                                                                                                                                                                                              if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  (SPMEVFILT2R_EL0_SysRegWrite_7e2235d697a1476e
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
                                                                                                                                                                                                                                                  if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      (SPMEVFILT2R_EL0_SysRegWrite_2b5e3e8ebfdd2403
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
                                                                                                                                                                                                                                                      if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          (SPMEVFILT2R_EL0_SysRegWrite_2a7524fd36300597
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
                                                                                                                                                                                                                                                          if ((((((CRm == 0b0111#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              (SPMEVFILT2R_EL0_SysRegWrite_50419316a0793567
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
                                                                                                                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  (SPMEVFILT2R_EL0_SysRegWrite_fc59638a1eed5ceb
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
                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      (SPMEVFILT2R_EL0_SysRegWrite_cb01e2f00db2e33f
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
                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          (SPMEVFILT2R_EL0_SysRegWrite_b606553f5e3a24b1
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
                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              (SPMEVFILT2R_EL0_SysRegWrite_3d2d295e35e201a9
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
                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  (SPMEVFILT2R_EL0_SysRegWrite_e72797af60944ed4
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
                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      (SPMEVFILT2R_EL0_SysRegWrite_3d27f26840346448
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
                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          (SPMEVFILT2R_EL0_SysRegWrite_4603ea69874f5bc4
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
                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b0110#4) && (CRn == 0b1110#4)) && (op0 == 0b10#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              (SPMEVFILT2R_EL0_SysRegWrite_f8ad05ef8935cee4
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
                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b1001#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  (ICC_AP1R_EL1_SysRegWrite_a8824fb00a7f4207
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
                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b1001#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      (ICC_AP1R_EL1_SysRegWrite_27852b8ac573cdcd
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
                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1001#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          (ICC_AP1R_EL1_SysRegWrite_0d9519f401c9d3ae
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
                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b1001#4) && (CRn == 0b1100#4)) && (op0 == 0b11#2)) && (op1 == 0b000#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              (ICC_AP1R_EL1_SysRegWrite_58ad13edd90bb69b
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
                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b0010#4) && (CRn == 0b0100#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  (DAIF_SysRegWrite_523f21b562245414
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
                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b0010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b101#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      (CNTP_CTL_EL0_SysRegWrite_6000d5c756b25763
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
                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          (PMEVCNTR_EL0_SysRegWrite_dd76d9177614ce63
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
                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              (PMEVCNTR_EL0_SysRegWrite_02fb1d66fa57255c
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
                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  (PMEVCNTR_EL0_SysRegWrite_9af53f393498a306
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
                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      (PMEVCNTR_EL0_SysRegWrite_728c6036c90b35ce
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
                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          (PMEVCNTR_EL0_SysRegWrite_ae5d8b12796ab9e6
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
                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              (PMEVCNTR_EL0_SysRegWrite_86cfe4162e1d3fcf
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
                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b1011#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  (PMEVCNTR_EL0_SysRegWrite_87d6d2e24b5727f8
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
                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      (PMEVCNTR_EL0_SysRegWrite_320d265a2d23e0ba
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
                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b110#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                          (PMEVCNTR_EL0_SysRegWrite_9bc9d4832692907c
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
                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b101#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                              (PMEVCNTR_EL0_SysRegWrite_77c9154118b31c0b
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
                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b100#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                  (PMEVCNTR_EL0_SysRegWrite_09863871a70add8c
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
                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b011#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                      (PMEVCNTR_EL0_SysRegWrite_7838a7b85145fa49
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
                                                                                                                                                                                                                                                                                                                                                                      if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b010#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                                                          (PMEVCNTR_EL0_SysRegWrite_984883ae00534017
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
                                                                                                                                                                                                                                                                                                                                                                          if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b001#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                                                              (PMEVCNTR_EL0_SysRegWrite_ff8724b529749d0c
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
                                                                                                                                                                                                                                                                                                                                                                              if ((((((CRm == 0b1010#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b000#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                                                  (PMEVCNTR_EL0_SysRegWrite_85d1907975c67ab9
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
                                                                                                                                                                                                                                                                                                                                                                                  if ((((((CRm == 0b1001#4) && (CRn == 0b1110#4)) && (op0 == 0b11#2)) && (op1 == 0b011#3)) && (op2 == 0b111#3)) : Bool)
                                                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                                                      (PMEVCNTR_EL0_SysRegWrite_25e19c40a7659e27
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
