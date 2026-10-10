module
public import QuantitativePaper.UniformScalarRootGrowthMomentBounds

@[expose] public section

/-! Genuine energy-CDF density formula and uniform derivative bound. The
terminal value is the smooth left representative, retaining the terminal
atom in the actual right CDF. -/
noncomputable section
open Set MeasureTheory Paper FRSB
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 2400000

theorem scalarRootGamma_le_CDF (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (q : ℝ) (hq : q∈Icc (0:ℝ) qtop) :
    scalarRootGamma β μ q≤β*parisiCDF μ q := by
  by_cases he : q=qtop
  · subst q
    rw [scalarRootGamma,←momentQuotient_terminal_mass_of_support_interval β hβ.ne' μ hmin
      qtop hqtop.1 hqtop.2.le hsupp]
    apply mul_le_mul_of_nonneg_left _ hβ.le
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (by intro x hx;change (x:ℝ)≤qtop;exact le_of_lt hx))
  · exact (scalarRootGamma_eq_CDF β hβ.ne' μ hmin qtop hqtop hsupp q
      ⟨hq.1,lt_of_le_of_ne hq.2 he⟩).le

theorem scalarRootGamma_density_formula (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (q : ℝ) (hq : q∈Icc (0:ℝ) qtop) :
    β*parisiSmoothDensity β μ qtop q=
      (scalarRootFourthSquare β μ q-12*scalarRootGamma β μ q*scalarRootMixedMoment β μ q+
        6*scalarRootGamma β μ q^2*scalarRootFourthMoment β μ q)/(2*scalarRootMomentB β μ q) := by
  rw [parisiSmoothDensity_eq_moment_formula_of_support_interval β hβ.ne' μ hmin qtop
    hqtop.1 hqtop.2.le hsupp q hq]
  have hB : quotientDenominator β μ q≠0 :=
    (quotientDenominator_pos β hβ.ne' μ q ⟨hq.1,hq.2.trans hqtop.2.le⟩).ne'
  simp only [quotientFourthSquarePolynomial,quotientFourthPowerPolynomial,moment_X_pow,
    moment_quotientMixedPolynomial,scalarRootFourthSquare,scalarRootGamma,
    scalarRootMixedMoment,scalarRootFourthMoment,scalarRootMomentB]
  field_simp <;> ring

def scalarRootDensityBound (K : ℝ) : ℝ := K^2+384*K^3+6144*K^4

theorem scalarRootMixedMoment_bound (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (K T : ℝ) (hK : 0≤K)
    (hjets : ∀j∈Finset.Icc 1 4,∀q∈Icc (0:ℝ) T,∀x,
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤K)
    (q : ℝ) (hq : q∈Icc (0:ℝ) T) : ‖scalarRootMixedMoment β μ q‖≤K^3 := by
  rw [scalarRootMixedMoment_eq]
  have hb : ∀ᵐsample∂canonicalBrownianMeasure,‖scalarRootJet β μ 1 q sample*
      scalarRootJet β μ 2 q sample^2‖≤K^3 := .of_forall fun sample=>by
    rw [norm_mul,norm_pow]
    have h1:=scalarRootJet_bound β hβ μ K T hjets 1 (by decide) q hq sample
    have h2:=pow_le_pow_left₀ (norm_nonneg _) (scalarRootJet_bound β hβ μ K T hjets 2 (by decide) q hq sample) 2
    have hh:=mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _) hK
    nlinarith
  simpa using norm_integral_le_of_norm_le_const hb

theorem scalarRootFourthMoment_bound (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (K T : ℝ) (hK : 0≤K)
    (hjets : ∀j∈Finset.Icc 1 4,∀q∈Icc (0:ℝ) T,∀x,
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤K)
    (q : ℝ) (hq : q∈Icc (0:ℝ) T) : ‖scalarRootFourthMoment β μ q‖≤K^4 := by
  rw [scalarRootFourthMoment_eq]
  have hb : ∀ᵐsample∂canonicalBrownianMeasure,‖scalarRootJet β μ 1 q sample^4‖≤K^4 := .of_forall fun sample=>by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (scalarRootJet_bound β hβ μ K T hjets 1 (by decide) q hq _) 4
  simpa using norm_integral_le_of_norm_le_const hb

theorem scalarRootGamma_density_bound (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (K T : ℝ) (hK : 0≤K)
    (hjets : ∀j∈Finset.Icc 1 4,∀q∈Icc (0:ℝ) T,∀x,
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤K)
    (q : ℝ) (hq : q∈Icc (0:ℝ) T) (hqt : q≤qtop)
    (hGamma : scalarRootGamma β μ q≤32) :
    ‖β*parisiSmoothDensity β μ qtop q‖≤ scalarRootDensityBound K := by
  have hqtop' : q∈Icc (0:ℝ) qtop:=⟨hq.1,hqt⟩
  have hB:=scalarRootMomentB_lower β hβ μ hmin qtop hqtop hsupp q hqtop'
  have hg0:=scalarRootGamma_nonneg β hβ.le μ q ⟨hq.1,hqt.trans hqtop.2.le⟩
  have hg : ‖scalarRootGamma β μ q‖≤32 := by rw [Real.norm_of_nonneg hg0];exact hGamma
  have hSQ : ‖scalarRootFourthSquare β μ q‖≤K^2 := by
    rw [Real.norm_of_nonneg (by rw [scalarRootFourthSquare_eq];exact integral_nonneg fun _=>sq_nonneg _)]
    exact scalarRootFourthSquare_bound β hβ.ne' μ K T hK hjets q hq
  have hM:=scalarRootMixedMoment_bound β hβ.ne' μ K T hK hjets q hq
  have hF:=scalarRootFourthMoment_bound β hβ.ne' μ K T hK hjets q hq
  have h12 : ‖12*scalarRootGamma β μ q*scalarRootMixedMoment β μ q‖≤384*K^3 := by
    simp only [norm_mul,Real.norm_ofNat]
    have hh:=mul_le_mul hg hM (norm_nonneg _) (by norm_num : (0:ℝ)≤32)
    nlinarith
  have h6 : ‖6*scalarRootGamma β μ q^2*scalarRootFourthMoment β μ q‖≤6144*K^4 := by
    simp only [norm_mul,Real.norm_ofNat,norm_pow]
    have hh:=mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hg 2) hF
      (norm_nonneg _) (by norm_num : (0:ℝ)≤(32:ℝ)^2)
    nlinarith
  have hNum : ‖scalarRootFourthSquare β μ q-12*scalarRootGamma β μ q*scalarRootMixedMoment β μ q+
      6*scalarRootGamma β μ q^2*scalarRootFourthMoment β μ q‖≤ scalarRootDensityBound K := by
    have h1:=norm_add_le (scalarRootFourthSquare β μ q-12*scalarRootGamma β μ q*scalarRootMixedMoment β μ q)
      (6*scalarRootGamma β μ q^2*scalarRootFourthMoment β μ q)
    have h2:=norm_sub_le (scalarRootFourthSquare β μ q) (12*scalarRootGamma β μ q*scalarRootMixedMoment β μ q)
    unfold scalarRootDensityBound
    linarith
  rw [scalarRootGamma_density_formula β hβ μ hmin qtop hqtop hsupp q hqtop',norm_div,
    Real.norm_of_nonneg (by linarith : 0≤2*scalarRootMomentB β μ q)]
  apply (div_le_iff₀ (by linarith : 0<2*scalarRootMomentB β μ q)).2
  have hp : 0≤ scalarRootDensityBound K := by unfold scalarRootDensityBound;positivity
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hB)]

end QuantitativePaper
