module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeNoisePhysical
public import QuantitativeFollowup.FollowupCavitySignedResponseScore

@[expose] public section

/-! Honest terminal Gibbs integration and the prescribed-root cancellation
identify the native Wiener score with the actual marked signed score. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem cavitySignedResponseFutureResidual_free_eq_full (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    (∫u,cavitySignedResponseFutureResidual D μ q u sample ∂parisiFreeMeasure μ a)=
      ∫u,cavitySignedResponseFutureResidual D μ q u sample ∂(μ:Measure Paper.Overlap) := by
  let f:=fun u=>cavitySignedResponseFutureResidual D μ q u sample
  have hm : Measurable f:=(measurable_uncurry_cavitySignedResponseFutureResidual D μ q).comp
    (measurable_id.prodMk measurable_const)
  have hi : Integrable f (parisiFreeMeasure μ a):=Integrable.of_bound hm.aestronglyMeasurable 2
    (.of_forall fun u=>norm_cavitySignedResponseFutureResidual_le D μ q u sample)
  haveI : IsFiniteMeasure (ENNReal.ofReal a •Measure.dirac zeroOverlap):=by
    constructor
    simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ _),smul_eq_mul,mul_one]
    exact ENNReal.ofReal_lt_top
  have hd : Integrable f (ENNReal.ofReal a •Measure.dirac zeroOverlap):=Integrable.of_bound hm.aestronglyMeasurable 2
    (.of_forall fun u=>norm_cavitySignedResponseFutureResidual_le D μ q u sample)
  rw [←root_add_parisiFreeMeasure μ a ha hμ,integral_add_measure hd hi]
  have h0 : f zeroOverlap=0:=by
    have hq : ¬q<zeroOverlap := not_lt.mpr (show zeroOverlap≤q from q.property.1)
    simp only [f,cavitySignedResponseFutureResidual,if_neg hq]
  simp only [integral_smul_measure,integral_dirac,h0,smul_zero,zero_add]
  rfl

theorem integral_anisotropicMeasureTerminalKernel_signed_score (D : AnisotropicSpinModel n)
    (hn : 0<n) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    (∫σ,cavitySignedResponseScore D μ a q (sample,σ) ∂anisotropicMeasureTerminalKernel D μ sample)=
      cavitySignedResponseWienerScore D μ q sample/(n:ℝ) := by
  classical
  have hn0 : (n:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hn)
  have hi (f : Configuration n→ℝ) : Integrable f (anisotropicMeasureTerminalKernel D μ sample):=
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  have hspin (i : Fin n) : (∫σ,Paper.spinSign (σ i) ∂anisotropicMeasureTerminalKernel D μ sample)=
      anisotropicProcessMagnetization D μ 1 sample i := by
    change anisotropicTerminalFeatureMean D (fun σ=>Paper.spinSign (σ i)) (anisotropicProcessParameter D μ 1 sample)=_
    exact (anisotropicProcessSpinResponse_one D μ _ i).symm
  have hterm : (∫σ,cavitySignedResponseTerminalResidual D μ q (sample,σ)
      ∂anisotropicMeasureTerminalKernel D μ sample)=
      inner ℝ (anisotropicProcessMagnetization D μ q sample)
        (anisotropicProcessMagnetization D μ 1 sample-anisotropicProcessMagnetization D μ q sample)/(n:ℝ) := by
    unfold cavitySignedResponseTerminalResidual
    rw [integral_div,integral_finsetSum Finset.univ (fun i _=>hi _)]
    simp only [cavitySignedResponseResidualCoordinate]
    simp_rw [integral_const_mul,integral_sub (hi _) (integrable_const _),hspin,integral_const,probReal_univ,one_smul]
    congr 1
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,PiLp.sub_apply,anisotropicProcessSpinResponse]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he (u : Paper.Overlap) : (if q<u then inner ℝ (anisotropicProcessMagnetization D μ q sample)
        (anisotropicProcessMagnetization D μ u sample-anisotropicProcessMagnetization D μ q sample) else 0)=
      (n:ℝ)*cavitySignedResponseFutureResidual D μ q u sample := by
    unfold cavitySignedResponseFutureResidual cavitySignedResponseMeanResidual
    split_ifs
    · rw [mul_div_cancel₀ _ hn0]
      simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,PiLp.sub_apply,anisotropicProcessSpinResponse]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [mul_zero]
  unfold cavitySignedResponseScore
  simp only [Prod.fst]
  rw [integral_sub (hi _) (integrable_const _),hterm,integral_const,probReal_univ,one_smul]
  unfold cavitySignedResponseWienerScore
  simp_rw [he]
  rw [integral_const_mul,←cavitySignedResponseFutureResidual_free_eq_full D μ a ha hμ q sample]
  unfold cavitySignedResponseIntegratedFutureResidual
  field_simp

end QuantitativeFollowup
