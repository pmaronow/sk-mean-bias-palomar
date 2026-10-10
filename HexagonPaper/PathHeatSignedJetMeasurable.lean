module
public import HexagonPaper.PathHeatSignedJet
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section

/-! Weak Borel measurability of actual signed path jets.  Auxiliary variables
need no total-variation continuity: directional difference quotients of the
measurable scalar functional identify every fixed-direction score, and another
sequence identifies every fixed-direction Hessian. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem measurable_pathHeatDirectionalJet
    {A V : Type*} [MeasurableSpace A]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (f : A×V→ℝ) (D : A×V→V→L[ℝ]ℝ)
    (hf : Measurable f)
    (hD : ∀a p,HasFDerivAt (fun q=>f (a,q)) (D (a,p)) p)
    (h : V) : Measurable (fun u=>D u h) := by
  let fseq : ℕ→A×V→ℝ := fun n u =>
    (n:ℝ) * (f (u.1,u.2+(n:ℝ)⁻¹ • h)-f u)
  apply measurable_of_tendsto_metrizable (f:=fseq)
  · intro n
    exact measurable_const.mul
      ((hf.comp (measurable_fst.prodMk (measurable_snd.add_const _))).sub hf)
  · rw [tendsto_pi_nhds]
    intro u
    exact ((hD u.1 u.2).lim_real h).comp
      tendsto_natCast_atTop_atTop

variable {A X : Type*} [TopologicalSpace A] [MeasurableSpace A]
  [OpensMeasurableSpace A] [SecondCountableTopology A]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [CompactSpace X] [SecondCountableTopology X]

local instance instMeasJetPathMeasurable : MeasurableSpace C(X,ℝ) := borel C(X,ℝ)
local instance instMeasJetPathBorel : BorelSpace C(X,ℝ) := ⟨rfl⟩

theorem measurable_pathHeatSignedScore_of_measurable_jets
    (f : A×C(X,ℝ)→ℝ) (S : A×C(X,ℝ)→SignedMeasure X)
    (hf : Measurable f)
    (hS : ∀a p,HasFDerivAt (fun q=>f (a,q)) (pathHeatSignedScore (S (a,p))) p)
    (h : C(X,ℝ)) : Measurable (fun u=>pathHeatSignedScore (S u) h) :=
  measurable_pathHeatDirectionalJet f (fun u=>pathHeatSignedScore (S u)) hf hS h

theorem measurable_pathHeatSignedScore_of_jets
    (f : A×C(X,ℝ)→ℝ) (S : A×C(X,ℝ)→SignedMeasure X)
    (hf : Continuous f)
    (hS : ∀a p,HasFDerivAt (fun q=>f (a,q)) (pathHeatSignedScore (S (a,p))) p)
    (h : C(X,ℝ)) : Measurable (fun u=>pathHeatSignedScore (S u) h) :=
  measurable_pathHeatSignedScore_of_measurable_jets f S hf.measurable hS h

theorem measurable_pathHeatSignedHessian_of_measurable_jets
    (f : A×C(X,ℝ)→ℝ) (S : A×C(X,ℝ)→SignedMeasure X)
    (M : A×C(X,ℝ)→SignedMeasure (X×X))
    (hf : Measurable f)
    (hS : ∀a p,HasFDerivAt (fun q=>f (a,q)) (pathHeatSignedScore (S (a,p))) p)
    (hM : ∀a p,HasFDerivAt (fun q=>pathHeatSignedScore (S (a,q)))
      (pathHeatSignedHessian (M (a,p))) p)
    (h k : C(X,ℝ)) : Measurable (fun u=>pathHeatSignedHessian (M u) h k) := by
  let D : A×C(X,ℝ)→C(X,ℝ)→L[ℝ]ℝ := fun u=>
    (ContinuousLinearMap.apply ℝ ℝ k).comp (pathHeatSignedHessian (M u))
  have hD : ∀a p,HasFDerivAt (fun q=>pathHeatSignedScore (S (a,q)) k) (D (a,p)) p := by
    intro a p
    exact (ContinuousLinearMap.apply ℝ ℝ k).hasFDerivAt.comp p (hM a p)
  exact measurable_pathHeatDirectionalJet
    (fun u=>pathHeatSignedScore (S u) k) D
    (measurable_pathHeatSignedScore_of_measurable_jets f S hf hS k) hD h

theorem measurable_pathHeatSignedHessian_of_jets
    (f : A×C(X,ℝ)→ℝ) (S : A×C(X,ℝ)→SignedMeasure X)
    (M : A×C(X,ℝ)→SignedMeasure (X×X))
    (hf : Continuous f)
    (hS : ∀a p,HasFDerivAt (fun q=>f (a,q)) (pathHeatSignedScore (S (a,p))) p)
    (hM : ∀a p,HasFDerivAt (fun q=>pathHeatSignedScore (S (a,q)))
      (pathHeatSignedHessian (M (a,p))) p)
    (h k : C(X,ℝ)) : Measurable (fun u=>pathHeatSignedHessian (M u) h k) :=
  measurable_pathHeatSignedHessian_of_measurable_jets f S M hf.measurable hS hM h k

end HexagonPaper
