module
public import QuantitativeFollowup.VectorQuantileTotalTail
public import FourPapersCommon.CubicSquareLayercake
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Literal integrated cubic and variance moments of the actual marked
self-overlap. Genuine product Fubini and weighted layer cake prove the
truncated identity used by Corollary 3.3. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorIntegratedSelfOverlapCubic (μ : Paper.ParisiMeasure) (s β t : ℝ) (ht : t≤1) : ℝ:=
  ∫v in Ioo (0:ℝ) (1-s),∫z,|vectorCenteredSelfOverlap (n:=n) μ β t ht (parisiFreeQuantile μ s v) z|^3
    ∂ vectorMeasureSpinPathLaw μ β t s ht

def vectorIntegratedSelfOverlapVariance (μ : Paper.ParisiMeasure) (s β t : ℝ) (ht : t≤1) : ℝ:=
  ∫v in Ioo (0:ℝ) (1-s),variance (vectorSelfOverlap (n:=n) μ β t ht (parisiFreeQuantile μ s v))
    (vectorMeasureSpinPathLaw μ β t s ht)

theorem vector_cubic_truncated_layercake (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) (1/2)) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (z : ℝ) (hz : z∈Ioc (0:ℝ) (1/4)) :
    vectorIntegratedSelfOverlapCubic (n:=n) μ s β t ht.le≤
      z*vectorIntegratedSelfOverlapVariance (n:=n) μ s β t ht.le+
      (∫θ in Ioo z (1/4),vectorIntegratedSelfOverlapSquareTail (n:=n) μ s β t ht.le θ)+
      (3/4)*vectorIntegratedSelfOverlapSquareTail (n:=n) μ s β t ht.le (1/4) :=by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t s ht.le
  let : IsProbabilityMeasure J:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t s ht.le
  let P:=volume.restrict (Ioo (0:ℝ) (1-s))
  let R:=P.prod J
  let f : ℝ×(VectorDisorderBrownianSample n×Configuration n)→ℝ:=
    fun p=>vectorCenteredSelfOverlap μ β t ht.le (parisiFreeQuantile μ s p.1) p.2
  have hInsert : Measurable (fun p : ℝ×(VectorDisorderBrownianSample n×Configuration n)=>
      (parisiFreeQuantile μ s p.1,p.2)):=
    ((parisiFreeQuantile_measurable μ s).comp measurable_fst).prodMk measurable_snd
  have hf : Measurable f:=by
    convert (measurable_uncurry_vectorCenteredSelfOverlap (n:=n) μ β t ht.le).comp hInsert using 1
    funext p
    rfl
  have hb (p : ℝ×(VectorDisorderBrownianSample n×Configuration n)) : |f p|≤1:=by
    simpa only [Real.norm_eq_abs] using norm_vectorCenteredSelfOverlap_le_one hn μ β t ht.le _ p.2
  have hiSq : Integrable (fun p=>f p^2) R:=Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable 1
    (.of_forall fun p=>by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr (hb p))
  have hiCube : Integrable (fun p=>|f p| ^ 3) R:=Integrable.of_bound (hf.abs.pow_const 3).aestronglyMeasurable 1
    (.of_forall fun p=>by
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hb p) 3)
  have hCube : (∫ p, (|f p| ^ 3) ∂ R)=vectorIntegratedSelfOverlapCubic (n:=n) μ s β t ht.le:=
    integral_prod _ hiCube
  have hSquare : (∫ p, f p^2 ∂ R)=vectorIntegratedSelfOverlapVariance (n:=n) μ s β t ht.le:=by
    rw [integral_prod _ hiSq]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro v hv
    exact vectorCenteredSelfOverlapSecond_free_quantile_variance hn μ s β t hβ ht
      ⟨hs.1,by linarith [hs.2]⟩ hμ hmin hv
  have hTail (θ : ℝ) :
      (∫ p, {p | θ < |f p| }.indicator (fun p=>f p^2) p ∂ R)=
        vectorIntegratedSelfOverlapSquareTail (n:=n) μ s β t ht.le θ:=by
    have hi:=hiSq.indicator (measurableSet_lt (measurable_const (a:=θ)) hf.abs)
    rw [integral_prod _ hi]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro v _
    apply integral_congr_ae
    exact .of_forall fun p=>by simp only [Set.indicator,mem_setOf_eq,f]
  have he:=cubic_moment_truncated_square_layercake R f hf hb z hz
  rw [hCube,hSquare,hTail (1/4)] at he
  have hTs : (fun θ=>(∫ p, {p | θ < |f p| }.indicator (fun p=>f p^2) p ∂ R))=
      vectorIntegratedSelfOverlapSquareTail (n:=n) μ s β t ht.le:=funext hTail
  rw [hTs] at he
  exact he

end QuantitativeFollowup
