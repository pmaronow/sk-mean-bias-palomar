module
public import HexagonPaper.PathHeatSignedJetMeasurable
public import QuantitativePaper.FiniteSpin
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

@[expose] public section

/-! Genuine finite-dimensional parameter jets are measurable from a measurable
scalar functional and smooth parameter sections. The retained record space
requires no topology. Difference quotients identify directional derivatives;
an actual continuous linear equivalence reconstructs the full operator. -/
noncomputable section
open Set Filter MeasureTheory QuantitativePaper
open scoped Topology ContDiff
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency true
variable {A F : Type} [MeasurableSpace A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {n : ℕ}

private theorem measurable_cavityDirectionalJet
    (f : A×Field n→F) (D : A×Field n→Field n→L[ℝ]F)
    (hf : Measurable f)
    (hD : ∀a p,HasFDerivAt (fun q=>f (a,q)) (D (a,p)) p)
    (h : Field n) : Measurable (fun u=>D u h) := by
  let fseq : ℕ→A×Field n→F := fun k u =>
    (k:ℝ) • (f (u.1,u.2+(k:ℝ)⁻¹ • h)-f u)
  apply measurable_of_tendsto_metrizable (f:=fseq)
  · intro k
    exact measurable_const.smul
      ((hf.comp (measurable_fst.prodMk (measurable_snd.add_const _))).sub hf)
  · rw [tendsto_pi_nhds]
    intro u
    exact ((hD u.1 u.2).lim_real h).comp tendsto_natCast_atTop_atTop

theorem measurable_cavityFiniteDerivative
    (f : A×Field n→F) (D : A×Field n→Field n→L[ℝ]F)
    (hf : Measurable f) (hD : ∀a p,HasFDerivAt (fun q=>f (a,q)) (D (a,p)) p) :
    Measurable D := by
  classical
  let e : Field n≃L[ℝ](Fin n→ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n=>ℝ)
  let T : (Field n→L[ℝ]F)≃L[ℝ](Fin n→F) :=
    (e.arrowCongr (ContinuousLinearEquiv.refl ℝ F)).trans
      (ContinuousLinearEquiv.piRing (𝕜:=ℝ) (E:=F) (Fin n))
  have hm : Measurable (fun u=>T (D u)) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_cavityDirectionalJet f D hf hD (e.symm (Pi.single i 1))
  have hh := T.symm.continuous.measurable.comp hm
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hh

theorem measurable_cavityFiniteFDeriv (f : A×Field n→F) (hf : Measurable f)
    (hs : ∀a,Differentiable ℝ (fun p=>f (a,p))) :
    Measurable (fun u : A×Field n=>fderiv ℝ (fun p=>f (u.1,p)) u.2) :=
  measurable_cavityFiniteDerivative f _ hf (fun a p=>(hs a p).hasFDerivAt)

local instance instCavityJetMultilinearMeasurable (r : ℕ) :
    MeasurableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin r=>Field n) F) := borel _
local instance instCavityJetMultilinearBorel (r : ℕ) :
    BorelSpace (ContinuousMultilinearMap ℝ (fun _ : Fin r=>Field n) F) := ⟨rfl⟩

local instance instCavityJetMultilinearSecondCountable (r : ℕ) :
    SecondCountableTopology (ContinuousMultilinearMap ℝ (fun _ : Fin r=>Field n) F) := by
  induction r with
  | zero => exact (continuousMultilinearCurryFin0 ℝ (Field n) F).toHomeomorph.secondCountableTopology
  | succ r ih =>
      letI := ih
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r+1)=>Field n) F).toHomeomorph.secondCountableTopology

theorem measurable_cavityFiniteIteratedFDeriv (f : A×Field n→F) (hf : Measurable f)
    (hs : ∀a,ContDiff ℝ ∞ (fun p=>f (a,p))) (r : ℕ) :
    Measurable (fun u : A×Field n=>iteratedFDeriv ℝ r (fun p=>f (u.1,p)) u.2) := by
  induction r with
  | zero =>
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def]
      exact (continuousMultilinearCurryFin0 ℝ (Field n) F).symm.continuous.measurable.comp hf
  | succ r ih =>
      have hm := measurable_cavityFiniteFDeriv
        (fun u=>iteratedFDeriv ℝ r (fun p=>f (u.1,p)) u.2) ih
        (fun a=>ContDiff.differentiable_iteratedFDeriv (m:=r) (n:=∞)
          (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top r)) (hs a))
      simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r+1)=>Field n) F).symm.continuous.measurable.comp hm

end HexagonPaper
