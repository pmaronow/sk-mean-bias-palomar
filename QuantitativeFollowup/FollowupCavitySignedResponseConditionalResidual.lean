module
public import QuantitativeFollowup.FollowupCavitySignedResponseResidualVariance
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

@[expose] public section

/-! The native two-time residual is a genuine conditional projection of
the terminal residual. Conditional expectation contraction yields its
sharp covariance-energy second-moment bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def cavitySignedResponseMeanResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap)
    (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  (∑i : Fin n,anisotropicProcessSpinResponse D μ r i sample*
    (anisotropicProcessSpinResponse D μ l i sample-anisotropicProcessSpinResponse D μ r i sample))/(n:ℝ)

theorem cavitySignedResponseTerminalResidual_condExp (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r l : Paper.Overlap) (hrl : r ≤ l) :
    (anisotropicMeasureSpinPathLaw D μ a)[cavitySignedResponseTerminalResidual D μ r|
      anisotropicSpinPast n (l:ℝ).toNNReal] =ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p => cavitySignedResponseMeanResidual D μ r l p.1 := by
  let P := anisotropicMeasureSpinPathLaw D μ a
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n×Configuration n) := inferInstance
  let V := anisotropicSpinPast n (l:ℝ).toNNReal
  letI : MeasurableSpace (AnisotropicDisorderBrownianSample n×Configuration n) := ambient
  let b := fun i : Fin n => fun p : AnisotropicDisorderBrownianSample n×Configuration n =>
    anisotropicProcessSpinResponse D μ r i p.1
  let X := fun i : Fin n => fun p : AnisotropicDisorderBrownianSample n×Configuration n =>
    Paper.spinSign (p.2 i)
  let W := fun p => (∑i : Fin n,b i p*X i p)/(n:ℝ)
  let d := fun p => (∑i : Fin n,b i p*b i p)/(n:ℝ)
  have hb (i : Fin n) : StronglyMeasurable[V] (b i) :=
    ((adapted_anisotropicProcessSpinResponse D μ r i).mono
      ((anisotropicBrownianFiltration n).mono (Real.toNNReal_mono hrl)) le_rfl).stronglyMeasurable.comp_measurable
      (comap_measurable Prod.fst)
  have hX (i : Fin n) : Measurable[Prod.instMeasurableSpace] (X i) :=
    (measurable_of_finite (fun σ : Configuration n => Paper.spinSign (σ i))).comp measurable_snd
  have hB (i : Fin n) (p) : ‖b i p‖ ≤ 1 := anisotropicProcessSpinResponse_bound D μ r i p.1
  have hXB (i : Fin n) (p) : ‖X i p‖ ≤ 1 := by
    simp only [X,Real.norm_eq_abs,Paper.abs_spinSign,le_refl]
  have hdknown : StronglyMeasurable[V] d := by
    have hh := Finset.stronglyMeasurable_sum Finset.univ (fun i _ => (hb i).mul (hb i))
    simpa only [d,div_eq_mul_inv,Finset.sum_apply,Pi.mul_apply] using hh.mul_const ((n:ℝ)⁻¹)
  have hdglobal := (hdknown.mono (anisotropicSpinPast_le n _)).measurable
  have hdB (p) : ‖d p‖ ≤ 1 := by
    have he : d p = anisotropicSelectedMeanSquare Finset.univ (anisotropicProcessMagnetization D μ r p.1) := by
      simp only [d,anisotropicSelectedMeanSquare,Finset.card_univ,Fintype.card_fin,←pow_two]
      rfl
    rw [he]
    exact anisotropicSelectedMeanSquare_bound _ _ (fun i => by
      exact anisotropicMeasureTailMagnetization_component_bound D μ r _ i)
  have hdi : Integrable d P := bounded_real_integrable d hdglobal 1 hdB
  have hwm : Measurable W :=
    (Finset.measurable_sum _ (fun i _ => ((hb i).mono (anisotropicSpinPast_le n _)).measurable.mul (hX i))).div_const _
  have hwB (p) : ‖W p‖ ≤ 1 := by
    by_cases hn : n=0
    · simp [W,hn]
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    change ‖(∑i : Fin n,b i p*X i p)/(n:ℝ)‖ ≤ 1
    rw [norm_div,Real.norm_of_nonneg hn0.le]
    apply (div_le_iff₀ hn0).2
    calc
      _ ≤ ∑i : Fin n,‖b i p*X i p‖ := norm_sum_le _ _
      _ ≤ ∑_i : Fin n,(1:ℝ) := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]
        exact (mul_le_mul (hB i p) (hXB i p) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
      _ = 1*(n:ℝ) := by simp
  have hwi : Integrable W P := bounded_real_integrable W hwm 1 hwB
  have hs := condExp_bounded_random_linear (P := P) V (anisotropicSpinPast_le n _) b X hb hX 1 zero_le_one hB hXB
  have hdiv : P[W|V] =ᵐ[P] fun p => P[(fun p => ∑i : Fin n,b i p*X i p)|V] p/(n:ℝ) := by
    have hh := condExp_smul (μ := P) ((n:ℝ)⁻¹) (fun p => ∑i : Fin n,b i p*X i p) V
    have he : ((n:ℝ)⁻¹ • (fun p => ∑i : Fin n,b i p*X i p)) = W := by
      funext p
      simp only [Pi.smul_apply,smul_eq_mul,W,div_eq_mul_inv,mul_comm]
    rw [he] at hh
    filter_upwards [hh] with p hp
    simpa only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm] using hp
  have hW : P[W|V] =ᵐ[P] fun p => (∑i : Fin n,b i p*anisotropicProcessSpinResponse D μ l i p.1)/(n:ℝ) := by
    filter_upwards [hdiv,hs,ae_all_iff.2 (fun i : Fin n => anisotropicMeasureSpinPathLaw_spin_condExp D μ a l i)]
      with p hp hs hall
    change P[W|V] p=(∑i : Fin n,b i p*anisotropicProcessSpinResponse D μ l i p.1)/(n:ℝ)
    rw [hp,hs]
    congr 1
    exact Finset.sum_congr rfl fun i _ => congrArg (fun x : ℝ => b i p*x) (hall i)
  have he : cavitySignedResponseTerminalResidual D μ r = W-d := by
    funext p
    simp only [cavitySignedResponseTerminalResidual,cavitySignedResponseResidualCoordinate,
      W,d,b,X,mul_sub,Finset.sum_sub_distrib,sub_div,Pi.sub_apply]
  rw [he]
  have hdce := condExp_of_stronglyMeasurable (anisotropicSpinPast_le n _) hdknown hdi
  have hsub := condExp_sub (m := V) hwi hdi
  filter_upwards [hsub,hW] with p hp hw
  change P[W-d|V] p=cavitySignedResponseMeanResidual D μ r l p.1
  rw [hp,Pi.sub_apply,hw,hdce]
  simp only [cavitySignedResponseMeanResidual,d,b,←sub_div,←Finset.sum_sub_distrib,mul_sub]

theorem cavitySignedResponseMeanResidual_second_moment_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r l : Paper.Overlap) (hrl : r ≤ l) :
    (∫sample,(cavitySignedResponseMeanResidual D μ r l sample)^2
      ∂anisotropicMeasureSampleLaw D μ a) ≤ cavitySignedResponseCovarianceMoment D μ a Finset.univ r := by
  let P := anisotropicMeasureSpinPathLaw D μ a
  let V := anisotropicSpinPast n (l:ℝ).toNNReal
  have hx := memLp_two_cavitySignedResponseTerminalResidual D μ a r
  have hi : Integrable (fun p => ‖cavitySignedResponseTerminalResidual D μ r p‖^(2:ℝ)) P := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using hx.integrable_sq
  have h := integral_norm_condExp_rpow_le (m := V) (by norm_num : (1:ℝ) ≤ 2) hi
  have hc := cavitySignedResponseTerminalResidual_condExp D μ a r l hrl
  have hl : (∫p,‖P[cavitySignedResponseTerminalResidual D μ r|V] p‖^(2:ℝ) ∂P) =
      ∫p,(cavitySignedResponseMeanResidual D μ r l p.1)^2 ∂P := by
    apply integral_congr_ae
    filter_upwards [hc] with p hp
    rw [hp,Real.rpow_two,Real.norm_eq_abs,sq_abs]
  rw [hl] at h
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs] at h
  rw [cavitySignedResponseTerminalResidual_second_moment] at h
  have hy : Measurable (cavitySignedResponseMeanResidual D μ r l) := by
    exact (Finset.measurable_sum _ (fun i _ =>
      (measurable_anisotropicProcessSpinResponse D μ r i).mul
        ((measurable_anisotropicProcessSpinResponse D μ l i).sub
          (measurable_anisotropicProcessSpinResponse D μ r i)))).div_const _
  rw [integral_anisotropicMeasureSpinPathLaw_sample D μ a _ (hy.pow_const 2)] at h
  exact h

end QuantitativeFollowup
