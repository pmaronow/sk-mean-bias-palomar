module
public import QuantitativeFollowup.FollowupCavitySignedResponseConditionalResidual

@[expose] public section

/-! Native measurability, boundedness and centering of the actual two-time
conditional residual. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem measurable_uncurry_cavitySignedResponseMeanResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r : Paper.Overlap) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      cavitySignedResponseMeanResidual D μ r z.1 z.2) := by
  have hm (i : Fin n) : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n =>
      anisotropicProcessSpinResponse D μ z.1 i z.2) := by
    have h := (EuclideanSpace.proj i).continuous.measurable.comp
      (measurable_uncurry_anisotropicProcessMagnetization D μ)
    exact h
  exact (Finset.measurable_sum _ (fun i _ =>
    ((measurable_anisotropicProcessSpinResponse D μ r i).comp measurable_snd).mul
      ((hm i).sub ((measurable_anisotropicProcessSpinResponse D μ r i).comp measurable_snd)))).div_const _

theorem measurable_cavitySignedResponseMeanResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap) :
    Measurable (cavitySignedResponseMeanResidual D μ r l) := by
  have hm : Measurable (fun sample : AnisotropicDisorderBrownianSample n => (l,sample)) :=
    measurable_const.prodMk measurable_id
  have hh := (measurable_uncurry_cavitySignedResponseMeanResidual D μ r).comp hm
  simpa only [Function.comp_def] using hh

theorem norm_cavitySignedResponseMeanResidual_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r l : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    ‖cavitySignedResponseMeanResidual D μ r l sample‖ ≤ 2 := by
  by_cases hn : n=0
  · simp [cavitySignedResponseMeanResidual,hn]
  have hn0 : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [cavitySignedResponseMeanResidual,norm_div,Real.norm_of_nonneg hn0.le]
  apply (div_le_iff₀ hn0).2
  calc
    _ ≤ ∑i : Fin n,‖anisotropicProcessSpinResponse D μ r i sample*
      (anisotropicProcessSpinResponse D μ l i sample-anisotropicProcessSpinResponse D μ r i sample)‖ :=
      norm_sum_le _ _
    _ ≤ ∑_i : Fin n,(2:ℝ) := Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      have hd := (norm_sub_le _ _).trans (add_le_add
        (anisotropicProcessSpinResponse_bound D μ l i sample)
        (anisotropicProcessSpinResponse_bound D μ r i sample))
      exact (mul_le_mul (anisotropicProcessSpinResponse_bound D μ r i sample) hd
        (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
    _ = 2*(n:ℝ) := by simp; ring

theorem memLp_two_cavitySignedResponseMeanResidual (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r l : Paper.Overlap) :
    MemLp (cavitySignedResponseMeanResidual D μ r l) 2 (anisotropicMeasureSampleLaw D μ a) :=
  MemLp.of_bound (measurable_cavitySignedResponseMeanResidual D μ r l).aestronglyMeasurable 2
    (.of_forall (norm_cavitySignedResponseMeanResidual_le D μ r l))

theorem cavitySignedResponseMeanResidual_centered (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r l : Paper.Overlap) (hrl : r≤l) :
    (∫sample,cavitySignedResponseMeanResidual D μ r l sample ∂anisotropicMeasureSampleLaw D μ a)=0 := by
  have hc := cavitySignedResponseTerminalResidual_condExp D μ a r l hrl
  have h1 := integral_anisotropicMeasureSpinPathLaw_sample D μ a
    (cavitySignedResponseMeanResidual D μ r l) (measurable_cavitySignedResponseMeanResidual D μ r l)
  have h2 : (∫p,(anisotropicMeasureSpinPathLaw D μ a)[cavitySignedResponseTerminalResidual D μ r|
      anisotropicSpinPast n (l:ℝ).toNNReal] p ∂anisotropicMeasureSpinPathLaw D μ a) =
    ∫p,cavitySignedResponseTerminalResidual D μ r p ∂anisotropicMeasureSpinPathLaw D μ a :=
      integral_condExp (anisotropicSpinPast_le n _)
  have h3 := integral_congr_ae hc
  exact h1.symm.trans (h3.symm.trans (h2.trans (cavitySignedResponseTerminalResidual_centered D μ a r)))

end QuantitativeFollowup
