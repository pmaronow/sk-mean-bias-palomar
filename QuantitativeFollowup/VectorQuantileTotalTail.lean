module
public import QuantitativeFollowup.VectorQuantileBinTailIntegral
public import FourPapersCommon.MonotoneFiniteBins

@[expose] public section

/-! The literal factor-170 integrated square-tail bound of Corollary 3.3,
from actual level bins and the proved per-bin conditional tail estimate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorIntegratedSelfOverlapSquareTail (μ : Paper.ParisiMeasure) (s β t : ℝ) (ht : t≤1)
    (θ : ℝ) : ℝ:=
  ∫v in Ioo (0:ℝ) (1-s),vectorSelfOverlapSquareTail (n:=n) μ β t s ht θ (parisiFreeQuantile μ s v)

theorem vector_quantile_total_square_tail (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) (1/2)) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hM : 1≤(n:ℝ)*((1-t)*β^2)) (θ : ℝ) (hθ : θ∈Ioc (0:ℝ) (1/4)) :
    vectorIntegratedSelfOverlapSquareTail (n:=n) μ s β t ht.le θ≤
      170*(1/((n:ℝ)*((1-t)*β^2)*s))*Real.log (2*((n:ℝ)*((1-t)*β^2)))/θ :=by
  classical
  let I:=Ioo (0:ℝ) (1-s)
  let f : ℝ→ℝ:=fun v=>(parisiFreeQuantile μ s v:ℝ)
  let g : ℝ→ℝ:=fun v=>vectorSelfOverlapSquareTail (n:=n) μ β t s ht.le θ (parisiFreeQuantile μ s v)
  let d:=θ/4
  let N:=Nat.ceil (1/d)+1
  let B : ℕ→Set ℝ:=monotoneFiniteBin I f 0 d
  let C:=34*(1/((n:ℝ)*((1-t)*β^2)*s))*Real.log (2*((n:ℝ)*((1-t)*β^2)))
  have hd : 0<d:=div_pos hθ.1 (by norm_num)
  have hf : Monotone f:=fun _ _ h=>parisiFreeQuantile_monotone μ s h
  have hg : Measurable g:=(measurable_vectorSelfOverlapSquareTail μ β t s ht.le θ).comp (parisiFreeQuantile_measurable μ s)
  have hCover : I=⋃k∈Finset.range N,B k:=
    monotoneFiniteBins_cover I f 0 d 1 hd (fun v _=>by simpa only [zero_add] using (parisiFreeQuantile μ s v).property)
  have hBOrd (k : ℕ) : (B k).OrdConnected:=
    monotoneFiniteBin_ordConnected I ordConnected_Ioo f hf 0 d hd k
  have hDom (k : ℕ) : B k⊆Ioc (0:ℝ) (1-s):=
    (monotoneFiniteBin_subset I f 0 d k).trans Ioo_subset_Ioc_self
  have hiB (k : ℕ) : IntegrableOn g (B k):=by
    let : IsFiniteMeasure (volume.restrict (B k)):=
      isFiniteMeasure_of_le (volume.restrict (Ioc (0:ℝ) (1-s))) (Measure.restrict_mono_set volume (hDom k))
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    exact .of_forall fun v=>by
      rw [Real.norm_of_nonneg (vectorSelfOverlapSquareTail_bounds hn μ β t s ht.le θ _).1]
      exact (vectorSelfOverlapSquareTail_bounds hn μ β t s ht.le θ _).2
  have hbin (k : ℕ) : (∫v in B k,g v)≤C:=by
    have hR:=monotoneFiniteBin_level_range I f 0 d hd (fun v _=>(parisiFreeQuantile μ s v).property.1) k
    have he:=vector_quantile_bin_tail_integral hn μ s β t hβ ht hs hμ hmin hM (B k)
      (hBOrd k) (hDom k) ((k:ℝ)*d) θ hθ.1 (by simpa only [zero_add] using hR)
    exact he
  unfold vectorIntegratedSelfOverlapSquareTail
  change (∫v in I,g v)≤_
  rw [hCover,integral_biUnion_finset (Finset.range N)
    (fun k _=>(hBOrd k).measurableSet)
    (fun i _ j _ hij=>monotoneFiniteBins_pairwiseDisjoint I f 0 d hij)
    (fun k _=>hiB k)]
  have hsumb:=Finset.sum_le_sum (fun k (_ : k∈Finset.range N)=>hbin k)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsumb
  have hc : (N:ℝ)≤1/d+2:=monotoneFiniteBins_count_bound d 1 hd zero_le_one
  have hc' : (N:ℝ)≤5/θ:=hc.trans (by
    dsimp only [d]
    rw [div_div_eq_mul_div,one_mul]
    apply (le_div_iff₀ hθ.1).mpr
    have he : (4/θ+2)*θ=4+2*θ:=by field_simp [hθ.1.ne'] <;> ring
    rw [he]
    linarith [hθ.2])
  have hC : 0≤C:=by
    apply mul_nonneg
      (mul_nonneg (by norm_num) (one_div_pos.mpr (mul_pos (zero_lt_one.trans_le hM) hs.1)).le)
    exact Real.log_nonneg (by linarith)
  apply hsumb.trans
  have he:=mul_le_mul_of_nonneg_right hc' hC
  convert he using 1 <;> dsimp only [C] <;> ring

end QuantitativeFollowup
