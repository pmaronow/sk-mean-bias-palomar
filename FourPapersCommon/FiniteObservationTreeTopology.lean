module
public import FourPapersCommon.FiniteObservationTreeTransport
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

@[expose] public section

/-! The genuine product topology of complete finite observation records. -/
noncomputable section
open MeasureTheory ProbabilityTheory TopologicalSpace
namespace FourPapersCommon.FiniteTerminalGenealogy
variable {E S : Type}

@[reducible] def recordTopologicalSpace (E S : Type) [TopologicalSpace E] [TopologicalSpace S] :
    {j : ℕ}→(T : FiniteTerminalGenealogy j)→TopologicalSpace (Records E S T)
  | _, .leaf => inferInstanceAs (TopologicalSpace S)
  | _, .advance T => @instTopologicalSpaceProd _ _ inferInstance (recordTopologicalSpace E S T)
  | _, .fork T U => @instTopologicalSpaceProd _ _
      (recordTopologicalSpace E S T) (recordTopologicalSpace E S U)

instance (priority := low) [TopologicalSpace E] [TopologicalSpace S] {j : ℕ} (T : FiniteTerminalGenealogy j) :
    TopologicalSpace (Records E S T):=recordTopologicalSpace E S T

instance (priority := low) [TopologicalSpace E] [TopologicalSpace S] [SecondCountableTopology E]
    [SecondCountableTopology S] {j : ℕ} (T : FiniteTerminalGenealogy j) :
    SecondCountableTopology (Records E S T) := by
  induction T with
  | leaf => exact inferInstanceAs (SecondCountableTopology S)
  | advance T ih =>
      haveI:=ih
      change SecondCountableTopology (E×Records E S T)
      infer_instance
  | fork T U ihT ihU =>
      haveI:=ihT
      haveI:=ihU
      change SecondCountableTopology (Records E S T×Records E S U)
      infer_instance

instance (priority := low) [TopologicalSpace E] [TopologicalSpace S] [PseudoMetrizableSpace E]
    [PseudoMetrizableSpace S] {j : ℕ} (T : FiniteTerminalGenealogy j) :
    PseudoMetrizableSpace (Records E S T) := by
  induction T with
  | leaf => exact inferInstanceAs (PseudoMetrizableSpace S)
  | advance T ih =>
      haveI:=ih
      change PseudoMetrizableSpace (E×Records E S T)
      infer_instance
  | fork T U ihT ihU =>
      haveI:=ihT
      haveI:=ihU
      change PseudoMetrizableSpace (Records E S T×Records E S U)
      infer_instance

instance (priority := low) [TopologicalSpace E] [TopologicalSpace S] [MeasurableSpace E] [MeasurableSpace S]
    [BorelSpace E] [BorelSpace S] [SecondCountableTopology E] [SecondCountableTopology S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) : BorelSpace (Records E S T) := by
  induction T with
  | leaf => exact inferInstanceAs (BorelSpace S)
  | advance T ih =>
      haveI:=ih
      change BorelSpace (E×Records E S T)
      infer_instance
  | fork T U ihT ihU =>
      haveI:=ihT
      haveI:=ihU
      change BorelSpace (Records E S T×Records E S U)
      infer_instance

instance (priority := low) [TopologicalSpace E] [TopologicalSpace S] [MeasurableSpace E] [MeasurableSpace S]
    [OpensMeasurableSpace E] [OpensMeasurableSpace S] [SecondCountableTopology E] [SecondCountableTopology S]
    {j : ℕ} (T : FiniteTerminalGenealogy j) : OpensMeasurableSpace (Records E S T) := by
  induction T with
  | leaf => exact inferInstanceAs (OpensMeasurableSpace S)
  | advance T ih =>
      haveI:=ih
      change OpensMeasurableSpace (E×Records E S T)
      infer_instance
  | fork T U ihT ihU =>
      haveI:=ihT
      haveI:=ihU
      change OpensMeasurableSpace (Records E S T×Records E S U)
      infer_instance

end FourPapersCommon.FiniteTerminalGenealogy
