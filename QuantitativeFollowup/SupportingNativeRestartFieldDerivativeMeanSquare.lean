module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeNative
public import QuantitativeFollowup.AnisotropicVarianceRestartConditional

@[expose] public section

/-! The C¹ restarted field expectation is the genuine native full-past
conditional future self-overlap, including equal observation times. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128

def anisotropicRestartMeanSquare (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (r : Paper.Overlap) : ℝ :=
  (∑i : Fin n, anisotropicRestartSpinSquare D μ g q x i r)/(n:ℝ)

theorem anisotropicRestartMeanSquare_eq_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (r : Paper.Overlap) :
    anisotropicRestartMeanSquare D μ g q x r =
      ∫sample,anisotropicSelectedMeanSquare Finset.univ
        (anisotropicMeasureTailMagnetization D μ r
          (anisotropicRestartPhysicalParameter D μ g q x ((r:ℝ)-(q:ℝ)).toNNReal sample))
        ∂vectorDisorderBrownianMeasure n := by
  have hi (i : Fin n) : Integrable
      (fun sample=>(anisotropicRestartSpinResponse D μ g q x i r sample)^2)
      (vectorDisorderBrownianMeasure n) :=
    Integrable.of_bound ((measurable_uncurry_anisotropicRestartSpinResponse D μ g q x i).of_uncurry_left.pow_const 2).aestronglyMeasurable 1 (.of_forall fun sample=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact (sq_le_one_iff_abs_le_one _).mpr
          (anisotropicRestartSpinResponse_abs_le D μ g q x i r sample))
  simp only [anisotropicSelectedMeanSquare,Finset.mem_univ,Finset.card_univ,Fintype.card_fin]
  change _ = ∫sample,(∑i : Fin n,(anisotropicRestartSpinResponse D μ g q x i r sample)^2)/(n:ℝ) ∂vectorDisorderBrownianMeasure n
  rw [integral_div,integral_finsetSum Finset.univ (fun i _=>hi i)]
  rfl

theorem contDiff_anisotropicRestartMeanSquare_field (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r : Paper.Overlap)
    (hqr : q≤r) : ContDiff ℝ 1 (fun x=>anisotropicRestartMeanSquare D μ g q x r) := by
  apply ContDiff.div_const
  exact ContDiff.sum fun i _=>contDiff_anisotropicRestartSpinSquare_field D μ g q r hqr i

theorem anisotropicRestartMeanSquare_condExp (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (outer : ℝ) (q r : Paper.Overlap) (hqr : q≤r) :
    (anisotropicMeasureSampleLaw D μ outer)[
      (fun sample=>anisotropicSelectedMeanSquare Finset.univ
        (anisotropicProcessMagnetization D μ r sample))|
      anisotropicBrownianFiltration n (q:ℝ).toNNReal]
      =ᵐ[anisotropicMeasureSampleLaw D μ outer]
      fun sample=>anisotropicRestartMeanSquare D μ sample.1 q
        (anisotropicMeasureState D μ q sample) r := by
  let P:=anisotropicMeasureSampleLaw D μ outer
  let m:=anisotropicBrownianFiltration n (q:ℝ).toNNReal
  let X:=fun i : Fin n=>fun sample : AnisotropicDisorderBrownianSample n=>
    (anisotropicProcessSpinResponse D μ r i sample)^2
  have hi (i : Fin n) : Integrable (X i) P :=
    Integrable.of_bound ((measurable_anisotropicProcessSpinResponse D μ r i).pow_const 2).aestronglyMeasurable 1 (.of_forall fun sample=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact (sq_le_one_iff_abs_le_one _).mpr
          (anisotropicMeasureTailMagnetization_component_bound D μ r _ i))
  have hs:=condExp_finsetSum (μ:=P) (s:=Finset.univ) (fun i _=>hi i) m
  have hc:=condExp_smul (μ:=P) ((n:ℝ)⁻¹) (∑i : Fin n,X i) m
  have hall:=ae_all_iff.2 fun i : Fin n=>anisotropicRestartConditionalSpinSquare_condExp
    D μ outer q r hqr i
  have he : (fun sample=>anisotropicSelectedMeanSquare Finset.univ
      (anisotropicProcessMagnetization D μ r sample))=(n:ℝ)⁻¹ •(∑i : Fin n,X i) := by
    funext sample
    simp only [anisotropicSelectedMeanSquare,Finset.card_univ,Fintype.card_fin,
      Pi.smul_apply,smul_eq_mul,Finset.sum_apply,X,div_eq_mul_inv,mul_comm]
    rfl
  rw [he]
  filter_upwards [hc,hs,hall] with sample hc hs hall
  rw [hc]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply,anisotropicRestartMeanSquare]
  rw [div_eq_mul_inv,mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (hall i).trans (anisotropicRestartConditionalSpinSquare_eq_restart D μ q r hqr i sample)

end QuantitativeFollowup
