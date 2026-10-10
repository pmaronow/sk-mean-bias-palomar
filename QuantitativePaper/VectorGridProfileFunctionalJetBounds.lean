module
public import QuantitativePaper.VectorGridProfileOuterNormalizedJetBounds
public import QuantitativePaper.VectorProfileAffineEndpointFunctional
public import QuantitativePaper.VectorProfileGridFunctionalIdentification
public import QuantitativePaper.VectorFunctionalSharpProfile

@[expose] public section

/-! The genuine full finite fractional functional has uniform second and
third profile jets. Its actual values converge uniformly on the closed
profile segment, including the ordinary-expectation outer branch. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorGridProfileFunctional (μ ν : Paper.ParisiMeasure) (β t lam : ℝ)
    (j : ℕ) : ℝ→ℝ:=
  vectorProfileAffineEnergyFunctional (n:=n)
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
    (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t lam

def vectorProfileFunctionalSecondJetBound (n : ℕ) (β t lam : ℝ) : ℝ:=
  vectorProfileOuterSecondJetBound n β t (lam/β)/|(n:ℝ)*β|

def vectorProfileFunctionalThirdJetBound (n : ℕ) (β t lam : ℝ) : ℝ:=
  vectorProfileOuterThirdJetBound n β t (lam/β)/|(n:ℝ)*β|

theorem vectorProfileFunctionalSecondJetBound_nonneg (n : ℕ) (β t lam : ℝ) (ht : t≤1) :
    0≤vectorProfileFunctionalSecondJetBound n β t lam:=
  div_nonneg (vectorProfileOuterSecondJetBound_nonneg n β t (lam/β) ht) (abs_nonneg _)

theorem vectorProfileFunctionalThirdJetBound_nonneg (n : ℕ) (β t lam : ℝ) (ht : t≤1) :
    0≤vectorProfileFunctionalThirdJetBound n β t lam:=
  div_nonneg (vectorProfileOuterThirdJetBound_nonneg n β t (lam/β) ht) (abs_nonneg _)

theorem vectorProfileAffineEnergyFunctional_third_derivative_eq {k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t lam θ : ℝ) :
    iteratedDeriv 3 (vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam) θ=
      iteratedDeriv 3 (vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam) θ := by
  have he : iteratedDeriv 2 (vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam)=
      iteratedDeriv 2 (vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam):=
    funext fun y=>vectorProfileAffineEnergyFunctional_second_derivative_eq s₀ s₁ β t lam y
  simpa only [iteratedDeriv_succ] using congrArg (fun f : ℝ→ℝ=>deriv f θ) he

theorem contDiff_vectorGridProfileFunctional (μ ν : Paper.ParisiMeasure) (β t lam : ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (vectorGridProfileFunctional (n:=n) μ ν β t lam j):=
  contDiff_vectorProfileAffineEnergyFunctional _ _ β t lam

theorem abs_vectorGridProfileFunctional_second_deriv_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (lam θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    |deriv (deriv (vectorGridProfileFunctional (n:=n) μ ν β t lam j)) θ|≤
      vectorProfileFunctionalSecondJetBound n β t lam := by
  have hb : |iteratedDeriv 2 (vectorGridProfileFunctional (n:=n) μ ν β t lam j) θ|≤
      vectorProfileFunctionalSecondJetBound n β t lam:=by
    unfold vectorGridProfileFunctional
    rw [vectorProfileAffineEnergyFunctional_second_derivative_eq]
    change |iteratedDeriv 2 (fun y=>vectorProfileOuterNormalized (n:=n) _ _ β t (lam/β) y/
      ((n:ℝ)*β)) θ|≤_
    rw [iteratedDeriv_div_const,abs_div]
    exact div_le_div_of_nonneg_right
      (abs_vectorGridProfileOuterNormalized_second_deriv_le μ ν j β t hβ ht (lam/β) θ hθ)
        (abs_nonneg _)
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hb

theorem abs_vectorGridProfileFunctional_third_deriv_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (lam θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    |deriv (deriv (deriv (vectorGridProfileFunctional (n:=n) μ ν β t lam j))) θ|≤
      vectorProfileFunctionalThirdJetBound n β t lam := by
  have hb : |iteratedDeriv 3 (vectorGridProfileFunctional (n:=n) μ ν β t lam j) θ|≤
      vectorProfileFunctionalThirdJetBound n β t lam:=by
    unfold vectorGridProfileFunctional
    rw [vectorProfileAffineEnergyFunctional_third_derivative_eq]
    change |iteratedDeriv 3 (fun y=>vectorProfileOuterNormalized (n:=n) _ _ β t (lam/β) y/
      ((n:ℝ)*β)) θ|≤_
    rw [iteratedDeriv_div_const,abs_div]
    exact div_le_div_of_nonneg_right
      (abs_vectorGridProfileOuterNormalized_third_deriv_le μ ν j β t hβ ht (lam/β) θ hθ)
        (abs_nonneg _)
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hb

theorem tendstoUniformlyOn_vectorGridProfileFunctional (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (β t lam : ℝ) (ht : t≤1) :
    TendstoUniformlyOn (vectorGridProfileFunctional (n:=n) μ ν β t lam)
      (fun θ=>responseEnergyFunctional n (Paper.parisiMix μ ν θ) β t lam)
        atTop (Icc (0:ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hzero : Tendsto (fun j : ℕ=>(((1-t)*β^2)/|β|)*
      (1/((vectorDyadicIndex j+1:ℕ):ℝ))) atTop (𝓝 0):=by
    simpa only [Nat.cast_add,Nat.cast_one,mul_zero,Function.comp_apply] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp tendsto_vectorDyadicIndex).const_mul
        (((1-t)*β^2)/|β|)
  filter_upwards [hzero.eventually (gt_mem_nhds hε)] with j hj
  intro θ hθ
  have he : vectorGridProfileFunctional (n:=n) μ ν β t lam j θ=
      responseEnergyFunctional n (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ)
        (vectorDyadicIndex j)) β t lam:=by
    unfold vectorGridProfileFunctional
    rw [←vectorProfileFiniteEnergyFunctional_eq_affine _ _ β t lam θ hθ]
    exact vectorProfile_grid_functional_eq μ ν j β t lam θ ht hθ
  rw [he,Real.dist_eq]
  change |vectorMeasureFunctional n (Paper.parisiMix μ ν θ) β t (lam/β)/β-
    vectorMeasureFunctional n (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ)
      (vectorDyadicIndex j)) β t (lam/β)/β|<ε
  rw [←sub_div,abs_div]
  apply lt_of_le_of_lt _ hj
  have hb:=div_le_div_of_nonneg_right
    (vectorMeasureFunctional_sharp_CDFDistance_abs_sub_le n hn (Paper.parisiMix μ ν θ)
      (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t (lam/β) ht)
    (abs_nonneg β)
  apply hb.trans
  have hc : 0≤((1-t)*β^2)/|β|:=div_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β)) (abs_nonneg β)
  convert mul_le_mul_of_nonneg_left (Paper.parisiCDFDistance_grid_le (Paper.parisiMix μ ν θ)
    (vectorDyadicIndex j)) hc using 1 <;>ring

end QuantitativePaper
