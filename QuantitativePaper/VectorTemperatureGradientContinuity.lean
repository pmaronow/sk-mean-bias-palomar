module
public import QuantitativePaper.VectorTemperaturePotentialContinuity
public import QuantitativePaper.VectorMeasureSpatialSmooth
public import QuantitativePaper.GradientStability
public import QuantitativePaper.VectorFiniteCellPDE

@[expose] public section

/-! Joint parameter/field gradient continuity obtained from true finite
differences and a uniform spatial Hessian bound. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem continuous_gradient_family_of_lipschitz_gradient {A : Type*} [TopologicalSpace A]
    (f : A → Field n → ℝ) (hF : Continuous (fun z : A × Field n => f z.1 z.2))
    (hf : ∀ a, Differentiable ℝ (f a)) (L : NNReal)
    (hL : ∀ a, LipschitzWith L (gradient (f a))) :
    Continuous (fun z : A × Field n => gradient (f z.1) z.2) := by
  have hc (i : Fin n) : Continuous (fun z : A × Field n => gradient (f z.1) z.2 i) := by
    let δ := fun j : ℕ => (1/2 : ℝ)^(j+1)
    have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
    let F := fun j (z : A × Field n) =>
      (f z.1 (z.2+δ j • EuclideanSpace.single i 1)-f z.1 z.2)/δ j
    have hu : TendstoUniformly F (fun z => gradient (f z.1) z.2 i) atTop := by
      apply Metric.tendstoUniformly_iff.mpr
      intro ε hε
      have hd : Tendsto (fun j => (L : ℝ)*δ j) atTop (𝓝 0) := by
        simpa only [δ,pow_succ,mul_zero,zero_mul] using
          ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
            (by norm_num : (1/2 : ℝ) < 1)).mul_const (1/2)).const_mul (L : ℝ)
      filter_upwards [hd.eventually (gt_mem_nhds hε)] with j hj
      intro z
      have hr := firstTaylor_remainder_of_lipschitz_fderiv (f z.1) (hf z.1) L
        (lipschitz_fderiv_of_lipschitz_gradient (f z.1) L (hL z.1))
        z.2 (δ j • EuclideanSpace.single i 1)
      have hn : ‖δ j • EuclideanSpace.single i (1 : ℝ)‖ = δ j := by
        rw [norm_smul,Real.norm_of_nonneg (hδ j).le,PiLp.norm_single,norm_one,mul_one]
      rw [hn] at hr
      have he : F j z-gradient (f z.1) z.2 i =
          (f z.1 (z.2+δ j • EuclideanSpace.single i 1)-f z.1 z.2-
            fderiv ℝ (f z.1) z.2 (δ j • EuclideanSpace.single i 1))/δ j := by
        dsimp only [F]
        rw [map_smul,smul_eq_mul,←gradient_euclidean_coordinate]
        field_simp [(hδ j).ne'] <;> ring
      rw [dist_eq_norm,norm_sub_rev,he,norm_div,Real.norm_of_nonneg (hδ j).le]
      calc
        _ ≤ (L : ℝ)*(δ j)^2/δ j := div_le_div_of_nonneg_right hr (hδ j).le
        _ = (L : ℝ)*δ j := by field_simp [(hδ j).ne'] <;> ring
        _ < ε := hj
    exact hu.continuous (.of_forall fun j =>
      (hF.comp (continuous_fst.prodMk (continuous_snd.add (continuous_const :
        Continuous (fun _ : A × Field n => δ j • EuclideanSpace.single i (1 : ℝ)))))).sub hF |>.div_const (δ j))
  convert (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp (continuous_pi hc) using 1
  funext z
  ext i
  rfl

theorem continuous_vectorMeasureGradient_temperature_field
    (μ : Paper.ParisiMeasure) (β : ℝ) (q : Paper.Overlap) (p : Couplings n × ℝ) :
    Continuous (fun z : Iio (1 : ℝ) × Field n => vectorMeasureGradient μ β z.1 q p z.2) := by
  let f := fun t : Iio (1 : ℝ) => vectorMeasureTailPotential μ β t q p
  have hL (t : Iio (1 : ℝ)) : LipschitzWith (n : NNReal) (gradient (f t)) := by
    have he : gradient (f t) = vectorMeasureGradient μ β t q p :=
      (funext (vectorMeasureGradient_eq_gradient μ β t t.property.le q p)).symm
    rw [he]
    exact vectorMeasureGradient_lipschitz μ β t t.property.le q p
  have h := continuous_gradient_family_of_lipschitz_gradient f
    (continuous_vectorMeasureTailPotential_temperature_field μ β q p)
    (fun t => (contDiff_vectorMeasureTailPotential μ β t t.property.le q p).differentiable (by simp))
    (n : NNReal) hL
  convert h using 1
  funext z
  exact vectorMeasureGradient_eq_gradient μ β z.1 z.1.property.le q p z.2

end QuantitativePaper
