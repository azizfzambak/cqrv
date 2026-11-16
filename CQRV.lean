import CQRV.Grades.Basic
import CQRV.Grades.Ext
import CQRV.Grades.Order
import CQRV.Grades.Hardware
import CQRV.Grades.Profile
import CQRV.Realizability.Basic
import CQRV.Realizability.Spec
import CQRV.Realizability.Realizes
import CQRV.Realizability.Composition
import CQRV.Realizability.MeasurePrepare
import CQRV.Realizability.TraceDistance
import CQRV.Realizability.Diamond
import CQRV.Realizability.Coherent
import CQRV.Realizability.Obstruction
import CQRV.Patterns.Basic
import CQRV.Patterns.Sound
import CQRV.Patterns.Select
import CQRV.DSL.Basic
import CQRV.Matching.Basic
import CQRV.Circuit.Basic
import CQRV.Circuit.MBUGeneral
import CQRV.Circuit.MBUClifford
import CQRV.Circuit.MBUBoundary
import CQRV.Circuit.RestoreAlgebra
import CQRV.Circuit.RestoreRegimes
import CQRV.Synthesis.MczFewK
import CQRV.Synthesis.Basic
import CQRV.Synthesis.Problem1
import CQRV.Certify.Basic
import CQRV.Certify.Specialize
import CQRV.Emit.Basic
import CQRV.Hardware.Target
import CQRV.Hardware.Bound
import CQRV.Hardware.Decomp
import CQRV.Hardware.DecompSound
import CQRV.Hardware.Relabel
import CQRV.Hardware.Route
import CQRV.Hardware.Witness
import CQRV.Hardware.Reorder
import CQRV.Hardware.WitnessSound
import CQRV.Hardware.Check
import CQRV.Hardware.CheckSound
import CQRV.Hardware.Noise
import CQRV.Hardware.NoiseCertGen
import CQRV.Noise.Perturb
import CQRV.Noise.Steps
import CQRV.Noise.Realize
import CQRV.Noise.Stochastic
import CQRV.Grover.CountingCorrect
import CQRV.Grover.Basic
import CQRV.Grover.SearchUnknownM
import CQRV.Grover.KGRegime

/-!
# CQRV

Root module of the CQRV package (report §9.1, §9.5.3): imports every
chapter-level component. See CLAUDE.md for the layout.
-/
