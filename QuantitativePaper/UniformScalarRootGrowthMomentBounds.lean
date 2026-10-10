module
public import QuantitativePaper.UniformScalarRootGrowthMoments

@[expose] public section

/-! Uniform root-moment bounds from actual energy-coordinate spatial jets
and the minimizing contact equation. No stochastic moment identity is an
extra premise. -/
noncomputable section
open Set MeasureTheory Paper FRSB
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 2400000

theorem scalarRootJet_bound (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (K T : ℝ) (hjets : ∀j∈Finset.Icc 1 4,∀q∈Icc (0:ℝ) T,∀x,
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤K)
    (j : ℕ) (hj : j∈Finset.Icc 1 4) (q : ℝ) (hq : q∈Icc (0:ℝ) T)
    (sample : Paper.BrownianSample) : ‖scalarRootJet β μ j q sample‖≤K := by
  rw [scalarRootJet_eq_energyJet β hβ]
  exact hjets j hj q hq _

theorem scalarRootGamma_nonneg (β : ℝ) (hβ : 0≤β) (μ : Paper.ParisiMeasure)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) : 0≤ scalarRootGamma β μ q := by
  by_cases hb : β=0
  · subst β
    simp [scalarRootGamma]
  · unfold scalarRootGamma momentQuotient
    exact mul_nonneg hβ (div_nonneg (quotientNumerator_nonneg _ _ _)
      (mul_pos (by norm_num) (quotientDenominator_pos β hb μ q hq)).le)

theorem scalarRootMixedMoment_nonneg (β : ℝ) (hβ : 0≤β) (μ : Paper.ParisiMeasure)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) : 0≤ scalarRootMixedMoment β μ q := by
  rw [scalarRootMixedMoment]
  exact mul_nonneg (pow_nonneg hβ _) (integral_nonneg fun sample=>
    mul_nonneg (C_pos β μ hq sample).le (sq_nonneg _))

theorem scalarRootMomentB_lower (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (q : ℝ) (hq : q∈Icc (0:ℝ) qtop) :
    1≤ scalarRootMomentB β μ q := by
  have hq1 : q∈Icc (0:ℝ) 1 := ⟨hq.1,hq.2.trans hqtop.2.le⟩
  have h2:=integrable_scalarRootJet_pow β hβ.ne' μ 1 2 q hq1
  have h3:=integrable_scalarRootJet_pow β hβ.ne' μ 1 3 q hq1
  have hh:=integral_mono ((h2.const_mul (3/2:ℝ)).sub (integrable_const (1/2:ℝ))) h3
    (fun sample=>by
      dsimp only [Pi.sub_apply]
      have hc:=(scalarRootJet_one_pos β hβ μ q hq1 sample).le
      nlinarith [mul_nonneg (sq_nonneg (scalarRootJet β μ 1 q sample-1))
        (by linarith : 0≤2*scalarRootJet β μ 1 q sample+1)])
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (h2.const_mul (3/2:ℝ)) (integrable_const (1/2:ℝ)),integral_const_mul,
    scalarRootContactMoment β hβ.ne' μ hmin qtop hqtop hsupp q hq,integral_const,
    ←scalarRootMomentB_eq] at hh
  norm_num at hh
  linarith

theorem scalarRootMomentB_upper (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (K T : ℝ)
    (hjets : ∀j∈Finset.Icc 1 4,∀q∈Icc (0:ℝ) T,∀x,
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤K)
    (q : ℝ) (hq : q∈Icc (0:ℝ) T) (hqt : q≤qtop) : scalarRootMomentB β μ q≤K := by
  have hq1 : q∈Icc (0:ℝ) 1 := ⟨hq.1,hqt.trans hqtop.2.le⟩
  have h2:=integrable_scalarRootJet_pow β hβ.ne' μ 1 2 q hq1
  have h3:=integrable_scalarRootJet_pow β hβ.ne' μ 1 3 q hq1
  have hh:=integral_mono h3 (h2.const_mul K) (fun sample=>by
    have hc:=scalarRootJet_bound β hβ.ne' μ K T hjets 1 (by decide) q hq sample
    have hl : scalarRootJet β μ 1 q sample≤K := (le_abs_self _).trans hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sq_nonneg (scalarRootJet β μ 1 q sample))])
  rw [integral_const_mul,scalarRootContactMoment β hβ.ne' μ hmin qtop hqtop hsupp q
    ⟨hq.1,hqt⟩,mul_one,←scalarRootMomentB_eq] at hh
  exact hh

theorem scalarRootFourthSquare_bound (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (K T : ℝ) (hK : 0≤K)
    (hjets : ∀j∈Finset.Icc 1 4,∀q∈Icc (0:ℝ) T,∀x,
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤K)
    (q : ℝ) (hq : q∈Icc (0:ℝ) T) : scalarRootFourthSquare β μ q≤K^2 := by
  rw [scalarRootFourthSquare_eq]
  apply (le_abs_self _).trans
  have hh : ∀ᵐsample∂canonicalBrownianMeasure,‖scalarRootJet β μ 3 q sample^2‖≤K^2 := .of_forall fun sample=>by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (scalarRootJet_bound β hβ μ K T hjets 3 (by decide) q hq _) 2
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hh

theorem scalarRootMomentA_linear_bound (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (K T : ℝ) (hK : 0≤K) (hT : 0≤T)
    (hTtop : T≤qtop)
    (hjets : ∀j∈Finset.Icc 1 4,∀q∈Icc (0:ℝ) T,∀x,
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤K)
    (q : ℝ) (hq : q∈Icc (0:ℝ) T) : scalarRootMomentA β μ q≤K^2*q := by
  have hcont:=((scalarRootMoments_contDiffOn β hβ.ne' μ hmin qtop hqtop hsupp).1.continuousOn).mono
    (Icc_subset_Icc le_rfl hTtop)
  have hd (r : ℝ) (hr : r∈Ioo (0:ℝ) T) :
      HasDerivAt (scalarRootMomentA β μ)
        (scalarRootFourthSquare β μ r-6*scalarRootGamma β μ r*scalarRootMixedMoment β μ r) r :=
    (scalarRootMomentA_hasDerivWithinAt β hβ.ne' μ hmin qtop hqtop hsupp r
      ⟨hr.1.le,hr.2.le.trans hTtop⟩).hasDerivAt (Icc_mem_nhds hr.1 (hr.2.trans_le hTtop))
  have hb (r : ℝ) (hr : r∈Ioo (0:ℝ) T) : deriv (scalarRootMomentA β μ) r≤K^2 := by
    rw [(hd r hr).deriv]
    have hr1 : r∈Icc (0:ℝ) 1 := ⟨hr.1.le,hr.2.le.trans (hTtop.trans hqtop.2.le)⟩
    have hg:=scalarRootGamma_nonneg β hβ.le μ r hr1
    have hm:=scalarRootMixedMoment_nonneg β hβ.le μ r hr1
    have he:=scalarRootFourthSquare_bound β hβ.ne' μ K T hK hjets r ⟨hr.1.le,hr.2.le⟩
    nlinarith [mul_nonneg hg hm]
  have hh:=(convex_Icc (0:ℝ) T).image_sub_le_mul_sub_of_deriv_le hcont
    (by rw [interior_Icc];exact fun r hr=>(hd r hr).differentiableAt.differentiableWithinAt)
    (by simpa only [interior_Icc] using hb) 0 ⟨le_rfl,hT⟩ q hq hq.1
  simpa only [scalarRootMomentA,quotientNumerator_initial_zero,mul_zero,sub_zero] using hh

theorem scalarRootGamma_linear_bound (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (K T : ℝ) (hK : 0≤K) (hT : 0≤T)
    (hTtop : T≤qtop)
    (hjets : ∀j∈Finset.Icc 1 4,∀q∈Icc (0:ℝ) T,∀x,
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤K)
    (q : ℝ) (hq : q∈Icc (0:ℝ) T) : scalarRootGamma β μ q≤K^2*q/2 := by
  have hB:=scalarRootMomentB_lower β hβ μ hmin qtop hqtop hsupp q ⟨hq.1,hq.2.trans hTtop⟩
  have hA:=scalarRootMomentA_linear_bound β hβ μ hmin qtop hqtop hsupp K T hK hT hTtop hjets q hq
  rw [scalarRootGamma_eq_quotient β hβ.ne']
  apply (div_le_iff₀ (by linarith : 0<2*scalarRootMomentB β μ q)).2
  have hn : 0≤K^2*q/2 := div_nonneg (mul_nonneg (sq_nonneg _) hq.1) (by norm_num)
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hB)]

end QuantitativePaper
