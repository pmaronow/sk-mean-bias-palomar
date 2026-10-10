module
public import QuantitativePaper.UniformScalarRootGrowthDensity
public import QuantitativePaper.ScalarSupportEndpointLower
public import QuantitativePaper.ScalarEnergyCrudeUpper
public import QuantitativePaper.ScalarEnergySublevel
public import FRSB.FullSupport

@[expose] public section

/-! Uniform upper growth and genuine Lipschitz regularity of the actual
minimizing energy CDF. The early strip is strictly inside the minimizing
support, uniformly for every beta above beta0, so the terminal atom is not
crossed in the derivative-to-Lipschitz passage. -/
noncomputable section
open Set MeasureTheory Paper FRSB
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 2400000

theorem scalarRootGamma_lipschitzOn (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (qtop : ℝ) (hqtop : qtop∈Ioo (0:ℝ) 1)
    (hsupp : parisiSupport μ=Icc (0:ℝ) qtop) (K T : ℝ) (hK : 0≤K) (hTtop : T≤qtop)
    (hjets : ∀j∈Finset.Icc 1 4,∀q∈Icc (0:ℝ) T,∀x,
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤K)
    (hcoeff : ∀q∈Icc (0:ℝ) T,β*parisiCDF μ q≤32) :
    LipschitzOnWith (scalarRootDensityBound K).toNNReal (scalarRootGamma β μ) (Icc 0 T) := by
  have hP : 0≤ scalarRootDensityBound K := by unfold scalarRootDensityBound;positivity
  apply (convex_Icc (0:ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f':=fun q=>β*parisiSmoothDensity β μ qtop q)
  · intro q hq
    exact (scalarRootGamma_hasDerivWithinAt β hβ.ne' μ hmin qtop hqtop hsupp q
      ⟨hq.1,hq.2.trans hTtop⟩).mono (Icc_subset_Icc le_rfl hTtop)
  · intro q hq
    apply NNReal.coe_le_coe.mp
    have hg : scalarRootGamma β μ q≤32 :=
      (scalarRootGamma_le_CDF β hβ μ hmin qtop hqtop hsupp q ⟨hq.1,hq.2.trans hTtop⟩).trans
        (hcoeff q hq)
    simpa only [coe_nnnorm,Real.coe_toNNReal _ hP] using
      scalarRootGamma_density_bound β hβ μ hmin qtop hqtop hsupp K T hK hjets q hq
        (hq.2.trans hTtop) hg

/-- Actual closed upper/Lipschitz family, uniform over all minimizing
measures and temperatures above beta0. No smoothing, support, or moment
premise is supplied to this endpoint. -/
theorem scalar_minimizer_uniform_root_upper_lipschitz (β0 : ℝ) (hβ0 : 1<β0) :
    ∃Cs Cac Tstar : ℝ,0<Cs ∧ 0<Cac ∧ Tstar∈Ioc (0:ℝ) (1/4) ∧
      ∀β : ℝ,β0≤β→∀μ : Paper.ParisiMeasure,IsParisiMinimizer β 0 μ→
        (∀q∈Icc (0:ℝ) Tstar,β*parisiCDF μ q≤Cs*q) ∧
        LipschitzOnWith Cac.toNNReal (fun q=>β*parisiCDF μ q) (Icc 0 Tstar) := by
  obtain ⟨K,hK,huniform⟩:=scalarEnergySpatialJet_uniform_early
  let delta:=1-1/β0
  let Tstar:=min (1/4:ℝ) (delta/2)
  have hδ : 0<delta := by
    unfold delta
    apply sub_pos.mpr
    exact (div_lt_iff₀ (zero_lt_one.trans hβ0)).2 (by simpa using hβ0)
  have hT : Tstar∈Ioc (0:ℝ) (1/4):=⟨lt_min (by norm_num) (half_pos hδ),min_le_left _ _⟩
  have hKpos : 0<K := zero_lt_one.trans_le hK
  have hP : 0<scalarRootDensityBound K := by unfold scalarRootDensityBound;positivity
  refine ⟨K^2/2,scalarRootDensityBound K,Tstar,by positivity,hP,hT,?_⟩
  intro β hβ0β μ hmin
  have hβ1 : 1<β:=hβ0.trans_le hβ0β
  have hβ : 0<β:=zero_lt_one.trans hβ1
  obtain ⟨qtop,hqtop,hsupp⟩:=minimizer_full_support β hβ1 μ hmin
  have hmem : qtop∈parisiSupport μ:=by rw [hsupp];exact ⟨hqtop.1.le,le_rfl⟩
  have htop:=scalar_support_max_ge_one_sub_inv β hβ μ hmin qtop hmem
    (fun q hq=>by rw [hsupp] at hq;exact hq.2)
  have hinv:=one_div_le_one_div_of_le (zero_lt_one.trans hβ0) hβ0β
  have hTtop : Tstar<qtop := by
    have hh : Tstar≤delta/2:=min_le_right _ _
    dsimp only [delta] at hh hδ
    linarith
  have hcost : scalarParisiFunctional β μ/β≤2:=
    (scalarEnergy_minimizer_cost_lt_three_halves β hβ1.le μ hmin).le.trans (by norm_num)
  have hjets (j : ℕ) (hj : j∈Finset.Icc 1 4) (q : ℝ) (hq : q∈Icc (0:ℝ) Tstar) (x : ℝ) :
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤K:=huniform β hβ μ hcost j hj q
        ⟨hq.1,hq.2.trans hT.2⟩ x
  have hcoeff (q : ℝ) (hq : q∈Icc (0:ℝ) Tstar) : β*parisiCDF μ q≤32 :=
    scalarEnergy_sublevel_two_cdf_le β hβ μ hcost q (hq.2.trans (hT.2.trans (by norm_num)))
  have heq (q : ℝ) (hq : q∈Icc (0:ℝ) Tstar) : scalarRootGamma β μ q=β*parisiCDF μ q :=
    scalarRootGamma_eq_CDF β hβ.ne' μ hmin qtop hqtop hsupp q ⟨hq.1,hq.2.trans_lt hTtop⟩
  refine ⟨fun q hq=>?_,?_⟩
  · have hh:=scalarRootGamma_linear_bound β hβ μ hmin qtop hqtop hsupp K Tstar hKpos.le
      hT.1.le hTtop.le hjets q hq
    rw [heq q hq] at hh
    simpa only [div_mul_eq_mul_div] using hh
  · have hl:=scalarRootGamma_lipschitzOn β hβ μ hmin qtop hqtop hsupp K Tstar hKpos.le
      hTtop.le hjets hcoeff
    intro q hq r hr
    change edist (β*parisiCDF μ q) (β*parisiCDF μ r) ≤ _
    rw [←heq q hq,←heq r hr]
    exact hl hq hr

end QuantitativePaper
