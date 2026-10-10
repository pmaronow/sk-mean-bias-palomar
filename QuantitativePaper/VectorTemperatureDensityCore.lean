module
public import QuantitativePaper.VectorTemperaturePotentialContinuity
public import QuantitativePaper.VectorExponentialLocalization
public import QuantitativePaper.VectorConditionalMomentTemperatureContinuityLaw
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Honest local Gaussian domination for the changing actual initial
potential. The fixed-base L² convergence lemma is proved by dominated
convergence of squared errors, not asserted for conditional moments. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem continuous_vectorMeasurePotential_initial_temperature (μ : Paper.ParisiMeasure)
    (β : ℝ) (p : Couplings n×ℝ) :
    Continuous (fun u:Iio (1:ℝ)=>vectorMeasurePotential μ β u p 0):=by
  have hm:Continuous (fun u:Iio (1:ℝ)=>(u,(0:Field n))):=
    continuous_id.prodMk continuous_const
  have hc:= (continuous_vectorMeasureTailPotential_temperature_field (n:=n) μ β (0:Paper.Overlap) p).comp hm
  have he:(fun u:Iio (1:ℝ)=>vectorMeasurePotential μ β u p 0)=
      fun u:Iio (1:ℝ)=>vectorMeasureTailPotential μ β u (0:Paper.Overlap) p 0:=by
    funext u
    exact (vectorMeasureTailPotential_zero μ β u u.property.le p 0).symm
  rw [he]
  exact hc

theorem vectorDisorderNormConstant_le_one_time (n : ℕ) (β t : ℝ) (ht:t≤1) :
    vectorDisorderNormConstant n β t≤vectorDisorderNormConstant n β 1:=by
  unfold vectorDisorderNormConstant
  gcongr

theorem vectorMeasurePotential_initial_temperature_local_bound (μ : Paper.ParisiMeasure)
    (β : ℝ) (t : Iio (1:ℝ)) :
    ∀ᶠu:Iio (1:ℝ) in 𝓝 t,∀p:Couplings n×ℝ,
      |vectorMeasurePotential μ β u p 0|≤
        (|vectorMeasurePotential (n:=n) μ β t (0,0) 0|+1)+vectorDisorderNormConstant n β 1*‖p‖:=by
  have hb:=((continuous_vectorMeasurePotential_initial_temperature (n:=n) μ β (0,0)).abs.tendsto t).eventually
    (gt_mem_nhds (by linarith:|vectorMeasurePotential (n:=n) μ β t (0,0) 0|<
      |vectorMeasurePotential (n:=n) μ β t (0,0) 0|+1))
  filter_upwards [hb] with u hu
  intro p
  have hd:=(vectorMeasurePotential_disorder_bound μ β u u.property.le p (0:Field n)).trans
    ((vectorDisorderEnvelope_le_norm n β u p).trans
      (mul_le_mul_of_nonneg_right (vectorDisorderNormConstant_le_one_time n β u u.property.le) (norm_nonneg _)))
  have he:=abs_add_le (vectorMeasurePotential (n:=n) μ β u (0,0) 0)
    (vectorMeasurePotential μ β u p 0-vectorMeasurePotential (n:=n) μ β u (0,0) 0)
  rw [add_sub_cancel] at he
  linarith

theorem vectorMeasurePotential_initial_temperature_bound_at (μ : Paper.ParisiMeasure)
    (β : ℝ) (t : Iio (1:ℝ)) (p:Couplings n×ℝ) :
    |vectorMeasurePotential μ β t p 0|≤
      (|vectorMeasurePotential (n:=n) μ β t (0,0) 0|+1)+vectorDisorderNormConstant n β 1*‖p‖:=by
  have hd:=(vectorMeasurePotential_disorder_bound μ β t t.property.le p (0:Field n)).trans
    ((vectorDisorderEnvelope_le_norm n β t p).trans
      (mul_le_mul_of_nonneg_right (vectorDisorderNormConstant_le_one_time n β t t.property.le) (norm_nonneg _)))
  have he:=abs_add_le (vectorMeasurePotential (n:=n) μ β t (0,0) 0)
    (vectorMeasurePotential μ β t p 0-vectorMeasurePotential (n:=n) μ β t (0,0) 0)
  rw [add_sub_cancel] at he
  linarith

/-- Dominated convergence of real representatives genuinely implies
norm convergence of their L² classes, for any countably generated filter. -/
theorem temperatureDensity_toLp_tendsto_of_dominated
    {Ω J : Type*} [MeasurableSpace Ω] {P:Measure Ω} {l:Filter J} [l.IsCountablyGenerated]
    (fj:J→Ω→ℝ) (f:Ω→ℝ) (hfj:∀j,MemLp (fj j) 2 P) (hf:MemLp f 2 P)
    (D:Ω→ℝ) (hD:Integrable (fun ω=>(D ω)^2) P)
    (hb:∀ᶠj in l,∀ᵐω∂P,‖fj j ω‖≤D ω)
    (hfb:∀ᵐω∂P,‖f ω‖≤D ω)
    (hlim:∀ᵐω∂P,Tendsto (fun j=>fj j ω) l (𝓝 (f ω))) :
    Tendsto (fun j=>(hfj j).toLp (fj j)) l (𝓝 (hf.toLp f)):=by
  have hd:Tendsto (fun j=>∫ω,(fj j ω-f ω)^2∂P) l (𝓝 0):=by
    have hh:=tendsto_integral_filter_of_dominated_convergence (μ:=P)
      (F:=fun j ω=>(fj j ω-f ω)^2) (f:=fun _=>(0:ℝ)) (fun ω=>4*(D ω)^2)
      (.of_forall fun j=>((hfj j).aestronglyMeasurable.sub hf.aestronglyMeasurable).pow 2)
      (hb.mono fun j hj=>by
        filter_upwards [hj,hfb] with ω hω hfω
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have he:=(norm_sub_le (fj j ω) (f ω)).trans (add_le_add hω hfω)
        have hp:=pow_le_pow_left₀ (norm_nonneg _) he 2
        simp only [Real.norm_eq_abs,sq_abs] at hp
        nlinarith only [hp])
      (hD.const_mul 4)
      (hlim.mono fun ω hω=>by simpa only [sub_self,zero_pow (by norm_num:2≠0)] using (hω.sub_const (f ω)).pow 2)
    simpa only [integral_zero] using hh
  have he (j:J):‖(hfj j).toLp (fj j)-hf.toLp f‖^2=∫ω,(fj j ω-f ω)^2∂P:=by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hfj j).toLp (fj j)) (hf.toLp f),(hfj j).coeFn_toLp,hf.coeFn_toLp]
      with ω hs hj hfω
    rw [hs,Pi.sub_apply,hj,hfω]
    simp only [RCLike.inner_apply,conj_trivial,pow_two]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hh:=Real.continuous_sqrt.continuousAt.tendsto.comp hd
  have heq (j:J):Real.sqrt (∫ω,(fj j ω-f ω)^2∂P)=‖(hfj j).toLp (fj j)-hf.toLp f‖:=by
    rw [←he,Real.sqrt_sq (norm_nonneg _)]
  simpa only [Function.comp_def,heq,Real.sqrt_zero] using hh

end QuantitativePaper
