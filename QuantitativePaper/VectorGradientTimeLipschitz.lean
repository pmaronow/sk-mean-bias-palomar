module
public import QuantitativePaper.VectorGradientTimeBounds
public import FourPapersCommon.FiniteCellLipschitz

@[expose] public section

/-! Genuine depth-independent time Lipschitz continuity of the actual
arbitrary-profile gradient. Finite cell derivatives are pasted across all
nodes and the proved uniform gradient limit preserves the estimate. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem vectorFiniteCellGradient_component_time_sub_le (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    {a b : ℝ} (ha : s.q i≤a) (hab : a≤b) (hb : b≤ s.q (i+1)) (x : Field n) (l : Fin n) :
    |gradient (vectorFiniteCellPotential (n:=n) s β t p i b) x l-
      gradient (vectorFiniteCellPotential (n:=n) s β t p i a) x l|≤vectorGradientTimeConstant n β t*(b-a) := by
  let g : ℝ→ℝ:=fun q=>gradient (vectorFiniteCellPotential (n:=n) s β t p i q) x l
  let d : ℝ→ℝ:=fun q=>-((1-t)*β^2)*vectorLinearBackwardGenerator
    (fun y=>gradient (vectorFiniteCellPotential (n:=n) s β t p i q) y l)
    (vectorFiniteCellPotential (n:=n) s β t p i q) (s.m i) x
  have hmap : Continuous (fun q : ℝ=>(q,x)):=continuous_id.prodMk continuous_const
  have hc:Continuous g:=by
    simpa only [g,Function.comp_def] using (continuous_vectorFiniteCellPotential_gradient_coordinate s β t p i l).comp hmap
  have hd : ∀q∈Ico a b,HasDerivWithinAt g (d q) (Ici q) q:=by
    intro q hq
    exact (hasDerivAt_vectorFiniteCellGradient_time s β t hβ ht p i q (hq.2.trans_le hb) x l).hasDerivWithinAt
  have hbound : ∀q∈Ico a b,‖d q‖≤vectorGradientTimeConstant n β t:=by
    intro q hq
    have hqcell:q∈Icc (s.q i) (s.q (i+1)):=⟨ha.trans hq.1,hq.2.le.trans hb⟩
    have hq01:q∈Icc (0:ℝ) 1:=⟨(s.q_nonneg (by omega)).trans hqcell.1,
      hqcell.2.trans (s.q_le_one (by omega))⟩
    exact norm_vectorFiniteCellGradient_timeDerivative_le s β t ht.le p i hi ⟨q,hq01⟩ hqcell x l
  simpa only [g,Real.norm_eq_abs] using
    norm_image_sub_le_of_norm_deriv_right_le_segment hc.continuousOn hd hbound b ⟨hab,le_rfl⟩

theorem vectorFiniteCellGradient_time_sub_le (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    {a b : ℝ} (ha : s.q i≤a) (hab : a≤b) (hb : b≤ s.q (i+1)) (x : Field n) :
    ‖gradient (vectorFiniteCellPotential (n:=n) s β t p i b) x-
      gradient (vectorFiniteCellPotential (n:=n) s β t p i a) x‖≤
      Real.sqrt (n:ℝ)*vectorGradientTimeConstant n β t*(b-a) := by
  let v:=gradient (vectorFiniteCellPotential (n:=n) s β t p i b) x-
    gradient (vectorFiniteCellPotential (n:=n) s β t p i a) x
  let R:=vectorGradientTimeConstant n β t*(b-a)
  have hR:0≤R:=mul_nonneg (vectorGradientTimeConstant_nonneg n β t ht.le) (sub_nonneg.mpr hab)
  have hs:‖v‖^2≤(n:ℝ)*R^2:=by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _≤∑_l : Fin n,R^2:=by
        apply Finset.sum_le_sum
        intro l _
        have hh:=vectorFiniteCellGradient_component_time_sub_le s β t hβ ht p i hi ha hab hb x l
        change |v l|≤R at hh
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hsq:(Real.sqrt (n:ℝ)*R)^2=(n:ℝ)*R^2:=by rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  have hb':‖v‖≤Real.sqrt (n:ℝ)*R:=by nlinarith [norm_nonneg v,mul_nonneg (Real.sqrt_nonneg (n:ℝ)) hR]
  simpa only [v,R,mul_assoc] using hb'

theorem vectorFiniteTailGradient_time_sub_le (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (p : Couplings n×ℝ) (q r : Paper.Overlap) (x : Field n) :
    ‖vectorFiniteTailGradient s β t q p x-vectorFiniteTailGradient s β t r p x‖≤
      Real.sqrt (n:ℝ)*vectorGradientTimeConstant n β t*|(q:ℝ)-(r:ℝ)| := by
  let F:=fun q : ℝ=>gradient (vectorTailRecursion s β t q p (k+2)) x
  have hcell : ∀i,i<k+2→∀{a b : ℝ},s.q i≤a→a≤b→b≤ s.q (i+1)→
      ‖F b-F a‖≤(Real.sqrt (n:ℝ)*vectorGradientTimeConstant n β t)*(b-a):=by
    intro i hi a b ha hab hb
    dsimp only [F]
    rw [vectorTailRecursion_eq_finiteCell s β t b p i (by omega) ⟨ha.trans hab,hb⟩,
      vectorTailRecursion_eq_finiteCell s β t a p i (by omega) ⟨ha,hab.trans hb⟩]
    exact vectorFiniteCellGradient_time_sub_le s β t hβ ht p i (by omega) ha hab hb x
  rcases le_total (r:ℝ) (q:ℝ) with h|h
  · have hh:=norm_sub_le_of_finite_interval_bounds F s.q (k+2) s.q_zero s.q_top
      (fun i hi=>s.q_mono' (i+1) (by omega) i (by omega)) _ hcell r.property q.property h
    simpa only [F,vectorFiniteTailGradient,abs_of_nonneg (sub_nonneg.mpr h)] using hh
  · have hh:=norm_sub_le_of_finite_interval_bounds F s.q (k+2) s.q_zero s.q_top
      (fun i hi=>s.q_mono' (i+1) (by omega) i (by omega)) _ hcell q.property r.property h
    rw [norm_sub_rev,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr h)]
    exact hh

theorem vectorMeasureGradient_time_sub_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (p : Couplings n×ℝ) (q r : Paper.Overlap) (x : Field n) :
    ‖vectorMeasureGradient μ β t q p x-vectorMeasureGradient μ β t r p x‖≤
      Real.sqrt (n:ℝ)*vectorGradientTimeConstant n β t*|(q:ℝ)-(r:ℝ)| := by
  apply le_of_tendsto ((tendsto_vectorDyadicTailGradient μ β t ht.le q p x).sub
    (tendsto_vectorDyadicTailGradient μ β t ht.le r p x)).norm
  exact Eventually.of_forall fun j=>vectorFiniteTailGradient_time_sub_le _ β t hβ ht p q r x

theorem vectorMeasureGradient_time_lipschitz (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (p : Couplings n×ℝ) (x : Field n) :
    LipschitzWith (Real.sqrt (n:ℝ)*vectorGradientTimeConstant n β t).toNNReal
      (fun q : Paper.Overlap=>vectorMeasureGradient μ β t q p x) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  rw [dist_eq_norm,Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _)
    (vectorGradientTimeConstant_nonneg n β t ht.le))]
  simpa only [Subtype.dist_eq,Real.dist_eq] using vectorMeasureGradient_time_sub_le μ β t hβ ht p q r x

end QuantitativePaper
