module
public import HexagonPaper.PathHeatWienerDifferentiation
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Continuous first derivatives and genuine one-sided endpoint derivatives
for the source Wiener heat formula. No positive clock variance is required
at the endpoints. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal BoundedContinuousFunction ContDiff
namespace HexagonPaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L : ℕ} {a b : ℝ}

theorem contDiffOn_one_of_hasDerivAt_of_continuous (f r : ℝ→ℝ) (a b : ℝ)
    (hr : Continuous r) (hf : ∀x,x∈Ioo a b→HasDerivAt f (r x) x) :
    ContDiffOn ℝ 1 f (Ioo a b) := by
  rw [show (1 : ℕ∞ω)=0+1 from rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun x hx=>(hf x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
  rw [contDiffOn_zero]
  exact hr.continuousOn.congr (fun x hx=>(hf x hx).deriv)

theorem pathHeatWiener_mixed_continuity
    (μ : Measure E) [IsGaussian μ] (hab : a≤b)
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (C : ℝ≥0) (hsource : PathHeatWienerAnalyticSource a b hab d C)
    (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (hc : ∀l,Continuous (fun z=>c z l)) (hdcc : ∀l,Continuous (fun z=>dc z l))
    (κ : ℝ≥0) (hD : ∀z,‖pathHeatClockRawKernel (dc z)‖≤κ) :
    Continuous (fun u=>pathHeatWienerSourceExpectation L μ d c (pathHeatTreeMixedOperator δ W) (projIcc a b hab u)) ∧
    Continuous (fun u=>pathHeatWienerSourceResponse L μ d c (pathHeatTreeMixedOperator δ W)
      (pathHeatTreeMixedKernelOperator δ W) (fun z=>pathHeatClockRawKernel (dc z)) (projIcc a b hab u)) ∧
    Continuous (fun u=>Real.log (pathHeatWienerSourceNormalizer L μ d c (pathHeatTreeMixedOperator δ W) (projIcc a b hab u))) ∧
    Continuous (fun u=>pathHeatWienerSourceLogNormalizerResponse L μ d c (pathHeatTreeMixedOperator δ W)
      (pathHeatTreeMixedKernelOperator δ W) (fun z=>pathHeatClockRawKernel (dc z)) (projIcc a b hab u)) := by
  letI : Nonempty (Icc a b) := ⟨⟨a,le_rfl,hab⟩⟩
  let T : C(Fin L×I,ℝ)→L[ℝ]C(Fin L×I,ℝ) := pathHeatTreeMixedOperator δ W
  let A : C(Fin L×I,C(Fin L×I,ℝ))→L[ℝ]C(Fin L×I,C(Fin L×I,ℝ)) := pathHeatTreeMixedKernelOperator δ W
  let D := fun z=>pathHeatClockRawKernel (dc z)
  let κA := pathHeatWienerMixedKernelBound δ W
  have hA : ∀k,‖A k‖≤κA*‖k‖ := fun k=>norm_pathHeatTreeMixedKernelOperator_apply_le δ W k
  have hDc : Continuous D := continuous_pathHeatRawClockKernel_family dc hdcc
  have hg : ∀z aux k p,|d.ell (z,((aux,k),p))|≤C*(1+‖aux‖+‖p‖) :=
    fun z aux k p=>hsource.ell_growth z (aux,k) p
  have hm := pathHeatWienerSource_continuous_moments L μ d c T A D κA κ C hA hDc hD hc hg
  have hl := pathHeatWienerSource_continuous_log_normalizer_response L μ d c T A D κA κ C hA hDc hD hc hg
  have hp (z : Icc a b) := pathHeatWienerSource_positive_normalizer L μ d c T A D κA κ C hA hD hg z
  exact ⟨hm.2.1.comp continuous_projIcc,hm.2.2.comp continuous_projIcc,
    (hm.1.log (fun z=>(hp z).ne')).comp continuous_projIcc,hl.comp continuous_projIcc⟩

theorem pathHeatWiener_mixed_C1_and_endpoints
    (μ : Measure E) [IsGaussian μ] (hab : a<b)
    (d : PathHeatContinuousSignedSource (Icc a b×((E×K)×C(Fin L×I,ℝ))) (Fin L×I))
    (C : ℝ≥0) (hsource : PathHeatWienerAnalyticSource a b hab.le d C)
    (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (hc : ∀l,Continuous (fun z=>c z l)) (hdcc : ∀l,Continuous (fun z=>dc z l))
    (hstrict : ∀z : Icc a b,z.val∈Ioo a b→∀l,StrictMono (c z l))
    (hroot : ∀z l,c z l 0=0)
    (hdc : ∀z∈Ioo a b,∀l t,
      HasDerivAt (fun u=>(c (projIcc a b hab.le u) l t:ℝ))
        (dc (projIcc a b hab.le z) l t) z)
    (κ : ℝ≥0) (hD : ∀z,‖pathHeatClockRawKernel (dc z)‖≤κ) :
    let f := fun u=>pathHeatWienerSourceExpectation L μ d c (pathHeatTreeMixedOperator δ W) (projIcc a b hab.le u)
    let r := fun u=>pathHeatWienerSourceResponse L μ d c (pathHeatTreeMixedOperator δ W)
      (pathHeatTreeMixedKernelOperator δ W) (fun z=>pathHeatClockRawKernel (dc z)) (projIcc a b hab.le u)
    let g := fun u=>Real.log (pathHeatWienerSourceNormalizer L μ d c (pathHeatTreeMixedOperator δ W) (projIcc a b hab.le u))
    let s := fun u=>pathHeatWienerSourceLogNormalizerResponse L μ d c (pathHeatTreeMixedOperator δ W)
      (pathHeatTreeMixedKernelOperator δ W) (fun z=>pathHeatClockRawKernel (dc z)) (projIcc a b hab.le u)
    ContDiffOn ℝ 1 f (Ioo a b) ∧ ContDiffOn ℝ 1 g (Ioo a b) ∧
    HasDerivWithinAt f (r a) (Ici a) a ∧ HasDerivWithinAt f (r b) (Iic b) b ∧
    HasDerivWithinAt g (s a) (Ici a) a ∧ HasDerivWithinAt g (s b) (Iic b) b := by
  dsimp only
  have hm := pathHeatWiener_mixed_continuity μ hab.le d C hsource c dc δ W hc hdcc κ hD
  have hderiv (x : ℝ) (hx : x∈Ioo a b) :=
    pathHeatWiener_mixed_differentiation μ hab.le d C hsource c dc δ W hc hdcc hstrict hroot hdc κ hD x hx
  have hf := fun x hx=>(hderiv x hx).2.1
  have hg := fun x hx=>(hderiv x hx).2.2
  have he := pathHeat_endpoint_derivatives _ _ a b hab hm.1.continuousOn hm.2.1.continuousOn hf
  have hl := pathHeat_endpoint_derivatives _ _ a b hab hm.2.2.1.continuousOn hm.2.2.2.continuousOn hg
  exact ⟨contDiffOn_one_of_hasDerivAt_of_continuous _ _ a b hm.2.1 hf,
    contDiffOn_one_of_hasDerivAt_of_continuous _ _ a b hm.2.2.2 hg,he.1,he.2,hl.1,hl.2⟩

end HexagonPaper
