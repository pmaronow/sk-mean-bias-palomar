module
public import FRSB.GammaPrime
public import FRSB.GammaEndpoints
public import FRSB.OptimalCurvatureMoment
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! Actual scalar diffusion kernel bounds used by the follow-up. Gamma,
magnetization and Hessian here are the constructed Brownian state and
the actual all-measure Parisi PDE, rather than supplied kernel moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 800000

theorem scalarGamma_nonneg (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ) :
    0 ≤ Gamma β μ p:=integral_nonneg (fun _=>sq_nonneg _)

theorem scalarGamma_le_one (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ)
    (hp : p∈Icc (0:ℝ) 1) : Gamma β μ p≤1 := by
  have hi:=integrable_M_sq β μ p hp
  have hb (ω : Paper.BrownianSample) : M β μ p ω^2≤1 := by
    have hh:=norm_parisiGradient_le_one β μ (p,optimalStateReal β μ ω p)
    have hm : |M β μ p ω|≤1:=by simpa only [M,jetProcess,parisiSpatialJet_one,Real.norm_eq_abs] using hh
    nlinarith [sq_abs (M β μ p ω),abs_nonneg (M β μ p ω),hm]
  have hh:=integral_mono hi (integrable_const (1:ℝ)) hb
  simpa only [Gamma,integral_const,probReal_univ,one_smul] using hh

theorem scalarGamma_interval_integral (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (r p : ℝ) (hr : r∈Icc (0:ℝ) 1) (hp : p∈Icc (0:ℝ) 1) :
    Gamma β μ p-Gamma β μ r=∫s in r..p,gammaCurvatureSource β hβ μ μ s := by
  have h0:=Gamma_integral β hβ μ hr
  have h1:=Gamma_integral β hβ μ hp
  have hi:=intervalIntegral.integral_interval_sub_left (μ:=volume)
    ((continuous_gammaCurvatureSource β hβ μ μ).intervalIntegrable 0 p)
    ((continuous_gammaCurvatureSource β hβ μ μ).intervalIntegrable 0 r)
  linarith

theorem scalarGamma_monotoneOn (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) :
    MonotoneOn (Gamma β μ) (Icc (0:ℝ) 1) := by
  intro r hr p hp hrp
  have hpos : 0≤∫s in r..p,gammaCurvatureSource β hβ μ μ s:=
    intervalIntegral.integral_nonneg hrp (fun s _=>integral_nonneg (fun ω=>mul_nonneg (sq_nonneg β) (sq_nonneg _)))
  rw [←scalarGamma_interval_integral β hβ μ r p hr hp] at hpos
  linarith

theorem scalarGamma_le_beta_sq_time (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (p : ℝ) (hp : p∈Icc (0:ℝ) 1) : Gamma β μ p≤β^2*p := by
  rw [Gamma_integral β hβ μ hp,Gamma_initial_zero β hβ μ,zero_add]
  have hb (s : ℝ) : gammaCurvatureSource β hβ μ μ s≤β^2 := by
    have hm : Measurable (selectedParisiItoState β 0 hβ μ s.toNNReal):=
      (boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).adapted_state _
      |>.measurable |>.mono (canonicalBrownianFiltration.le _) le_rfl
    have hf : Integrable (fun ω=>β^2*parisiSpatialJet β μ 2 s
        (selectedParisiItoState β 0 hβ μ s.toNNReal ω)^2) canonicalBrownianMeasure:=by
      simp only [parisiSpatialJet_two]
      apply (integrable_const (β^2)).mono'
        (measurable_const.mul (((continuous_parisiHessian_all β μ).measurable.comp
          (measurable_const.prodMk hm)).pow_const 2)).aestronglyMeasurable
      filter_upwards with ω
      change ‖β^2*parisiHessian β μ (s,selectedParisiItoState β 0 hβ μ s.toNNReal ω)^2‖≤β^2
      rw [norm_mul,Real.norm_of_nonneg (sq_nonneg β),norm_pow]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (norm_parisiHessian_le_one_all _ _ _))
        (sq_nonneg β)).trans_eq (by ring)
    have hh:=integral_mono hf (integrable_const (β^2)) (fun ω=>by
      rw [parisiSpatialJet_two]
      have hn:=norm_parisiHessian_le_one_all β μ (s,selectedParisiItoState β 0 hβ μ s.toNNReal ω)
      have hs : parisiHessian β μ (s,selectedParisiItoState β 0 hβ μ s.toNNReal ω)^2≤1:=by
        simpa only [Real.norm_eq_abs,sq_abs] using pow_le_one₀ (n:=2) (norm_nonneg _) hn
      exact (mul_le_mul_of_nonneg_left hs (sq_nonneg β)).trans_eq (mul_one _))
    simpa only [gammaCurvatureSource,integral_const,probReal_univ,one_smul] using hh
  have hic : IntervalIntegrable (fun _s : ℝ=>β^2) volume 0 p:=intervalIntegrable_const
  have hh:=intervalIntegral.integral_mono_on (μ:=volume) hp.1
    ((continuous_gammaCurvatureSource β hβ μ μ).intervalIntegrable 0 p) hic
    (fun s _=>hb s)
  simpa [mul_comm] using hh

theorem scalarGamma_bound (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (p : ℝ) (hp : p∈Icc (0:ℝ) 1) :
    0≤Gamma β μ p ∧ Gamma β μ p ≤ min 1 (β^2*p) :=
  ⟨scalarGamma_nonneg β μ p,le_min (scalarGamma_le_one β μ p hp)
    (scalarGamma_le_beta_sq_time β hβ μ p hp)⟩

theorem scalarGamma_window_bound (β d : ℝ) (hβ : 0<β)
    (hd : d∈Icc (β^2/2) (β^2)) (μ : Paper.ParisiMeasure) (p : ℝ) (hp : p∈Icc (0:ℝ) 1) :
    0≤Gamma (Real.sqrt d) μ p ∧ Gamma (Real.sqrt d) μ p ≤ min 1 (d*p) ∧
      min 1 (d*p) ≤ min 1 (β^2*p) := by
  have hd0 : 0<d:=by nlinarith [hd.1,sq_pos_of_pos hβ]
  have hb:=scalarGamma_bound (Real.sqrt d) (Real.sqrt_pos.mpr hd0).ne' μ p hp
  rw [Real.sq_sqrt hd0.le] at hb
  exact ⟨hb.1,hb.2,min_le_min_left 1 (mul_le_mul_of_nonneg_right hd.2 hp.1)⟩

theorem scalarCurvature_unit_bound (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (p : ℝ) (hp : p∈Icc (0:ℝ) 1) (ω : Paper.BrownianSample) :
    0<C β μ p ω ∧ C β μ p ω≤1-M β μ p ω^2 := by
  have hpos:=parisiHessian_pos β hβ μ p (optimalStateReal β μ ω p) hp
  have hb:=parisiHessian_add_gradient_sq_le_one β hβ μ (p,optimalStateReal β μ ω p)
  simp only [C,M,jetProcess,parisiSpatialJet_two,parisiSpatialJet_one] at *
  exact ⟨hpos,by linarith⟩

theorem scalar_M_sq_C_bound (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (p : ℝ) (hp : p∈Icc (0:ℝ) 1) :
    0≤(∫ω,M β μ p ω^2*C β μ p ω∂canonicalBrownianMeasure) ∧
      (∫ω,M β μ p ω^2*C β μ p ω∂canonicalBrownianMeasure)≤Gamma β μ p := by
  have hi : Integrable (fun ω=>M β μ p ω^2*C β μ p ω) canonicalBrownianMeasure:=by
    apply (integrable_M_sq β μ p hp).mul_bdd (c:=1)
      (measurable_C β hβ μ hp).aestronglyMeasurable
    filter_upwards with ω
    simp only [C,jetProcess,parisiSpatialJet_two]
    exact norm_parisiHessian_le_one_all _ _ _
  refine ⟨integral_nonneg (fun ω=>mul_nonneg (sq_nonneg _) (scalarCurvature_unit_bound β hβ μ p hp ω).1.le),?_⟩
  apply integral_mono hi (integrable_M_sq β μ p hp)
  intro ω
  have hc:=scalarCurvature_unit_bound β hβ μ p hp ω
  have hc1 : C β μ p ω≤1:=by linarith [sq_nonneg (M β μ p ω)]
  exact (mul_le_mul_of_nonneg_left hc1 (sq_nonneg _)).trans_eq (mul_one _)

theorem scalar_square_variance_bound (β : ℝ) (μ : Paper.ParisiMeasure)
    (p : ℝ) (hp : p∈Icc (0:ℝ) 1) :
    0≤variance (fun ω=>M β μ p ω^2) canonicalBrownianMeasure ∧
      variance (fun ω=>M β μ p ω^2) canonicalBrownianMeasure≤Gamma β μ p := by
  have hb (ω : Paper.BrownianSample) : ‖M β μ p ω‖≤1:=by
    simpa only [M,jetProcess,parisiSpatialJet_one] using norm_parisiGradient_le_one β μ (p,optimalStateReal β μ ω p)
  have hf : MemLp (fun ω=>M β μ p ω^2) 2 canonicalBrownianMeasure:=
    MemLp.of_bound ((measurable_M β μ p hp).pow_const 2).aestronglyMeasurable 1
      (.of_forall fun ω=>by rw [norm_pow];exact pow_le_one₀ (norm_nonneg _) (hb ω))
  refine ⟨variance_nonneg _ _,?_⟩
  rw [variance_eq_sub hf]
  have hi:=integral_mono hf.integrable_sq (integrable_M_sq β μ p hp) (fun ω=>by
    have hsq : M β μ p ω^2≤1:=by
      have hh:=hb ω
      rw [Real.norm_eq_abs] at hh
      nlinarith [sq_abs (M β μ p ω),abs_nonneg (M β μ p ω)]
    simpa only [pow_two,mul_one] using mul_le_mul_of_nonneg_left hsq (sq_nonneg (M β μ p ω)))
  change (∫ω,(M β μ p ω^2)^2∂canonicalBrownianMeasure)-(Gamma β μ p)^2≤Gamma β μ p
  change (∫ω,(M β μ p ω^2)^2∂canonicalBrownianMeasure)≤Gamma β μ p at hi
  linarith [sq_nonneg (Gamma β μ p)]

end QuantitativeFollowup
