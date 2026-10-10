module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileIntegral
public import QuantitativeFollowup.AnisotropicNoiseProfileStability
public import QuantitativeFollowup.FollowupCavityRestProcess

@[expose] public section

/-! Genuine common-driver weak-profile convergence of the complete native
rest self-overlap path, uniformly over its physical observation level. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128

def cavityNativeProfileStateError (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) : ℝ :=
  ‖anisotropicNoiseMap D‖ *
    (anisotropicNoiseProfileError D μ ν * Real.exp (anisotropicWhitenedDriftLip D))

theorem norm_anisotropicMeasureState_profile_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (q : Paper.Overlap)
    (ω : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicMeasureState D μ q ω-anisotropicMeasureState D ν q ω‖≤
      cavityNativeProfileStateError D μ ν := by
  have hμ := anisotropicMeasureState_restart D μ 0 q q.property.1 ω
  have hν := anisotropicMeasureState_restart D ν 0 q q.property.1 ω
  simp only [Set.Icc.coe_zero,anisotropicMeasureState_zero,map_zero,sub_zero] at hμ hν
  rw [hμ,hν,←map_sub]
  apply ((anisotropicNoiseMap D).le_opNorm _).trans
  have hb := norm_anisotropicRestartNoiseStatePath_profile_sub_le D μ ν ω.1 0 0 0
    (fun i => canonicalFutureBrownianPath (Real.toNNReal (0:ℝ)) (ω.2 i)) (q:ℝ)
    (by simpa using q.property)
  simp only [Set.Icc.coe_zero,sub_zero,sub_self,norm_zero,zero_add] at hb
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

def cavityNativeProfileMeanError (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) : ℝ :=
  anisotropicProfileGradientError D μ ν +
    (‖anisotropicResponseMap n‖*‖anisotropicEnergyMap D‖^2)*
      (‖anisotropicFieldInjection n‖*cavityNativeProfileStateError D μ ν)

theorem cavityNativeProfileMeanError_nonneg (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) : 0≤cavityNativeProfileMeanError D μ ν := by
  unfold cavityNativeProfileMeanError cavityNativeProfileStateError
  positivity [anisotropicProfileGradientError_nonneg D μ ν,
    anisotropicNoiseProfileError_nonneg D μ ν]

theorem norm_anisotropicProcessMagnetization_profile_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (q : Paper.Overlap)
    (ω : AnisotropicDisorderBrownianSample n) :
    ‖anisotropicProcessMagnetization D μ q ω-anisotropicProcessMagnetization D ν q ω‖≤
      cavityNativeProfileMeanError D μ ν := by
  let P := anisotropicProcessParameter D μ q ω
  let Q := anisotropicProcessParameter D ν q ω
  have hPQ : ‖P-Q‖≤‖anisotropicFieldInjection n‖*cavityNativeProfileStateError D μ ν := by
    dsimp only [P,Q,anisotropicProcessParameter]
    rw [add_sub_add_left_eq_sub,←map_sub]
    exact ((anisotropicFieldInjection n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left
        (norm_anisotropicMeasureState_profile_sub_le D μ ν q ω) (norm_nonneg _))
  have hLip := (anisotropicMeasureTailMagnetization_lipschitz D ν q).norm_sub_le P Q
  simp only [NNReal.coe_mul,NNReal.coe_pow,coe_nnnorm] at hLip
  change ‖anisotropicMeasureTailMagnetization D μ q P-
    anisotropicMeasureTailMagnetization D ν q Q‖≤_
  calc
    _≤‖anisotropicMeasureTailMagnetization D μ q P-anisotropicMeasureTailMagnetization D ν q P‖+
       ‖anisotropicMeasureTailMagnetization D ν q P-anisotropicMeasureTailMagnetization D ν q Q‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤anisotropicProfileGradientError D μ ν+
      (‖anisotropicResponseMap n‖*‖anisotropicEnergyMap D‖^2)*
        (‖anisotropicFieldInjection n‖*cavityNativeProfileStateError D μ ν) :=
      add_le_add (norm_anisotropicMeasureTailMagnetization_profile_sub_le D μ ν q P)
        (hLip.trans (mul_le_mul_of_nonneg_left hPQ (by positivity)))
    _=cavityNativeProfileMeanError D μ ν := rfl

theorem tendsto_cavityNativeProfileMeanError {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) :
    Tendsto (fun j => cavityNativeProfileMeanError D (μ j) ν) l (𝓝 0) := by
  have hd := FRSB.tendsto_parisiCDFDistance_of_tendsto hμ
  have hG := tendsto_anisotropicProfileGradientError D μ ν hd
  have hS := ((tendsto_anisotropicNoiseProfileError D μ ν hd).mul_const
    (Real.exp (anisotropicWhitenedDriftLip D))).const_mul ‖anisotropicNoiseMap D‖
  have ht := hG.add ((hS.const_mul ‖anisotropicFieldInjection n‖).const_mul
    (‖anisotropicResponseMap n‖*‖anisotropicEnergyMap D‖^2))
  simpa only [cavityNativeProfileMeanError,cavityNativeProfileStateError,mul_zero,zero_mul,zero_add] using ht

theorem tendsto_anisotropicProcessMagnetization_profile_time {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) {q : I→Paper.Overlap} {r : Paper.Overlap}
    (hq : Tendsto q l (𝓝 r)) (ω : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun j => anisotropicProcessMagnetization D (μ j) (q j) ω) l
      (𝓝 (anisotropicProcessMagnetization D ν r ω)) := by
  have hf := (continuous_anisotropicProcessMagnetization_time D ν ω).tendsto r |>.comp hq
  have he := squeeze_zero (fun j => norm_nonneg _)
    (fun j => norm_anisotropicProcessMagnetization_profile_sub_le D (μ j) ν (q j) ω)
    (tendsto_cavityNativeProfileMeanError D hμ)
  exact tendsto_of_tendsto_of_dist hf (by
    simpa only [dist_eq_norm,Function.comp_def,norm_sub_rev] using he)

theorem tendsto_anisotropicMeasureState_profile_time {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) {q : I→Paper.Overlap} {r : Paper.Overlap}
    (hq : Tendsto q l (𝓝 r)) (ω : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun j => anisotropicMeasureState D (μ j) (q j) ω) l
      (𝓝 (anisotropicMeasureState D ν r ω)) := by
  have hf := ((continuous_anisotropicMeasureState D ν ω).comp continuous_subtype_val).tendsto r |>.comp hq
  have hE : Tendsto (fun j => cavityNativeProfileStateError D (μ j) ν) l (𝓝 0) := by
    simpa only [cavityNativeProfileStateError,mul_zero,zero_mul] using
      ((tendsto_anisotropicNoiseProfileError D μ ν (FRSB.tendsto_parisiCDFDistance_of_tendsto hμ)).mul_const
        (Real.exp (anisotropicWhitenedDriftLip D))).const_mul ‖anisotropicNoiseMap D‖
  have he := squeeze_zero (fun j => norm_nonneg _)
    (fun j => norm_anisotropicMeasureState_profile_sub_le D (μ j) ν (q j) ω) hE
  exact tendsto_of_tendsto_of_dist hf (by
    simpa only [dist_eq_norm,Function.comp_def,norm_sub_rev] using he)

theorem tendsto_anisotropicProcessParameter_profile_time {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) {q : I→Paper.Overlap} {r : Paper.Overlap}
    (hq : Tendsto q l (𝓝 r)) (ω : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun j => anisotropicProcessParameter D (μ j) (q j) ω) l
      (𝓝 (anisotropicProcessParameter D ν r ω)) :=
  tendsto_const_nhds.add ((anisotropicFieldInjection n).continuous.tendsto _ |>.comp
    (tendsto_anisotropicMeasureState_profile_time D hμ hq ω))

theorem anisotropicSelectedMeanSquare_sub_le (x y : Field n)
    (hx : ∀i,|x i|≤1) (hy : ∀i,|y i|≤1) :
    ‖anisotropicSelectedMeanSquare Finset.univ x-
      anisotropicSelectedMeanSquare Finset.univ y‖≤2*‖x-y‖ := by
  by_cases hn : n=0
  · simp [anisotropicSelectedMeanSquare,hn]
  have hn0 : 0<(n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hi (i : Fin n) : ‖(x i)^2-(y i)^2‖≤2*‖x-y‖ := by
    have hd : |x i-y i|≤‖x-y‖ := by
      simpa only [Real.norm_eq_abs,PiLp.sub_apply] using PiLp.norm_apply_le (x-y) i
    have hs : |x i+y i|≤2 := (abs_add_le _ _).trans (by linarith [hx i,hy i])
    rw [Real.norm_eq_abs,show (x i)^2-(y i)^2=(x i-y i)*(x i+y i) by ring,abs_mul]
    exact (mul_le_mul hd hs (abs_nonneg _) (norm_nonneg _)).trans_eq (by ring)
  simp only [anisotropicSelectedMeanSquare,Finset.card_univ,Fintype.card_fin,
    ←sub_div,←Finset.sum_sub_distrib,norm_div,Real.norm_of_nonneg hn0.le]
  apply (div_le_iff₀ hn0).mpr
  exact ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>hi i)).trans_eq
    (by simp;ring)

theorem norm_cavityRestOverlapPath_profile_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (ω : AnisotropicDisorderBrownianSample n) :
    ‖cavityRestOverlapPath D μ ω-cavityRestOverlapPath D ν ω‖≤
      2*cavityNativeProfileMeanError D μ ν := by
  apply (ContinuousMap.norm_le _ (by positivity [cavityNativeProfileMeanError_nonneg D μ ν])).mpr
  intro q
  exact (anisotropicSelectedMeanSquare_sub_le _ _
    (fun i=>anisotropicMeasureTailMagnetization_component_bound D μ q _ i)
    (fun i=>anisotropicMeasureTailMagnetization_component_bound D ν q _ i)).trans
      (mul_le_mul_of_nonneg_left
        (norm_anisotropicProcessMagnetization_profile_sub_le D μ ν q ω) (by norm_num))

theorem tendsto_cavityRestOverlapPath_profile {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (ω : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun j => cavityRestOverlapPath D (μ j) ω) l (𝓝 (cavityRestOverlapPath D ν ω)) := by
  have he := (tendsto_cavityNativeProfileMeanError D hμ).const_mul 2
  have ht := squeeze_zero (fun j => norm_nonneg _)
    (fun j => norm_cavityRestOverlapPath_profile_sub_le D (μ j) ν ω)
    (by simpa only [mul_zero] using he)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr ht

end QuantitativeFollowup
