module
public import QuantitativeFollowup.AnisotropicSpinPathConditionals
public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section

/-! Two fresh terminal marks are sampled independently from the genuine
regular conditional terminal-spin distribution given the whole native past.
They are distinct draws, including when their sampled configurations agree. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def anisotropicPastTerminalSpinKernel (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : Paper.Overlap) :
    @Kernel (AnisotropicDisorderBrownianSample n×Configuration n) (Configuration n)
      (anisotropicSpinPast n (q:ℝ).toNNReal) inferInstance := by
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n×Configuration n):=inferInstance
  let V:=anisotropicSpinPast n (q:ℝ).toNNReal
  exact @condDistrib (AnisotropicDisorderBrownianSample n×Configuration n)
    (AnisotropicDisorderBrownianSample n×Configuration n) (Configuration n)
    inferInstance inferInstance inferInstance ambient V Prod.snd id
    (anisotropicMeasureSpinPathLaw D μ a) inferInstance

instance anisotropicPastTerminalSpinKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    IsMarkovKernel (anisotropicPastTerminalSpinKernel D μ a q) := by
  unfold anisotropicPastTerminalSpinKernel
  infer_instance

def anisotropicFreshTerminalSpinKernel (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : Paper.Overlap) :
    Kernel (AnisotropicDisorderBrownianSample n×Configuration n) (Configuration n) :=
  (anisotropicPastTerminalSpinKernel D μ a q).comap id
    (@measurable_id'' (AnisotropicDisorderBrownianSample n×Configuration n)
      (anisotropicSpinPast n (q:ℝ).toNNReal) inferInstance (anisotropicSpinPast_le n _))

instance anisotropicFreshTerminalSpinKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    IsMarkovKernel (anisotropicFreshTerminalSpinKernel D μ a q) := by
  unfold anisotropicFreshTerminalSpinKernel
  infer_instance

def anisotropicFreshTerminalPairLaw (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : Paper.Overlap) :
    Measure ((AnisotropicDisorderBrownianSample n×Configuration n)×(Configuration n×Configuration n)) :=
  (anisotropicMeasureSpinPathLaw D μ a) ⊗ₘ
    ((anisotropicFreshTerminalSpinKernel D μ a q) ×ₖ (anisotropicFreshTerminalSpinKernel D μ a q))

instance anisotropicFreshTerminalPairLaw_probability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    IsProbabilityMeasure (anisotropicFreshTerminalPairLaw D μ a q) := by
  unfold anisotropicFreshTerminalPairLaw
  infer_instance

theorem anisotropicFreshTerminalSpinKernel_conditional_mean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (f : Configuration n→ℝ) :
    (anisotropicMeasureSpinPathLaw D μ a)[(fun p=>f p.2)|anisotropicSpinPast n (q:ℝ).toNNReal]=ᵐ[
      anisotropicMeasureSpinPathLaw D μ a]
      (fun p=>∫σ,f σ∂anisotropicFreshTerminalSpinKernel D μ a q p) := by
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n×Configuration n):=inferInstance
  let V:=anisotropicSpinPast n (q:ℝ).toNNReal
  let C:=∑σ : Configuration n,‖f σ‖
  have hi : Integrable (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>f p.2)
      (anisotropicMeasureSpinPathLaw D μ a):=(integrable_const C).mono'
      ((measurable_of_finite f).comp measurable_snd).aestronglyMeasurable
      (.of_forall fun p=>Finset.single_le_sum (fun σ _=>norm_nonneg (f σ)) (Finset.mem_univ p.2))
  have he:=@condExp_ae_eq_integral_condDistrib
    (AnisotropicDisorderBrownianSample n×Configuration n)
    (AnisotropicDisorderBrownianSample n×Configuration n) (Configuration n) ℝ
    inferInstance inferInstance inferInstance inferInstance ambient
    (anisotropicMeasureSpinPathLaw D μ a) inferInstance id Prod.snd V inferInstance inferInstance
    (@measurable_id'' _ V ambient (anisotropicSpinPast_le n _)) measurable_snd.aemeasurable
    f (measurable_of_finite f).stronglyMeasurable hi
  simpa only [MeasurableSpace.comap_id,id_eq,anisotropicFreshTerminalSpinKernel,
    Kernel.comap_apply,anisotropicPastTerminalSpinKernel,V] using he

private theorem fresh_pair_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (f : Configuration n→ℝ) :
    (∫z,f z.2.1*f z.2.2∂anisotropicFreshTerminalPairLaw D μ a q)=
      ∫p,(∫σ,f σ∂anisotropicFreshTerminalSpinKernel D μ a q p)^2
        ∂anisotropicMeasureSpinPathLaw D μ a := by
  let C:=∑σ : Configuration n,‖f σ‖
  have hC : 0≤C:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have hb (σ : Configuration n) : ‖f σ‖≤C:=
    Finset.single_le_sum (fun τ _=>norm_nonneg (f τ)) (Finset.mem_univ σ)
  have hi : Integrable (fun z : (AnisotropicDisorderBrownianSample n×Configuration n)×
      (Configuration n×Configuration n)=>f z.2.1*f z.2.2) (anisotropicFreshTerminalPairLaw D μ a q) :=
    (integrable_const (C^2)).mono'
      (((measurable_of_finite f).comp measurable_snd.fst).mul
        ((measurable_of_finite f).comp measurable_snd.snd)).aestronglyMeasurable
      (.of_forall fun z=>by rw [norm_mul];exact (mul_le_mul (hb _) (hb _) (norm_nonneg _) hC).trans_eq (by ring))
  rw [anisotropicFreshTerminalPairLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun p=>by
    simp only [Kernel.prod_apply]
    rw [integral_prod_mul,pow_two]

theorem anisotropicFreshTerminalPairLaw_pair_square (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    (∫z,(Paper.spinSign (z.2.1 e.1.1)*Paper.spinSign (z.2.1 e.1.2))*
      (Paper.spinSign (z.2.2 e.1.1)*Paper.spinSign (z.2.2 e.1.2))
        ∂anisotropicFreshTerminalPairLaw D μ a q)=
      ∫p,(anisotropicProcessPairResponse D μ q e p)^2∂anisotropicMeasureSampleLaw D μ a := by
  rw [fresh_pair_integral D μ a q (fun σ=>Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2))]
  have hk:=(anisotropicFreshTerminalSpinKernel_conditional_mean D μ a q
    (fun σ=>Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2))).symm.trans
      (anisotropicMeasureSpinPathLaw_pair_condExp D μ a q e)
  have hs : (fun p=>(∫σ,Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)
      ∂anisotropicFreshTerminalSpinKernel D μ a q p)^2)=ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      (fun p=>(anisotropicProcessPairResponse D μ q e p.1)^2) := by
    filter_upwards [hk] with p hp using congrArg (fun x : ℝ=>x^2) hp
  rw [integral_congr_ae hs]
  exact integral_anisotropicMeasureSpinPathLaw_sample D μ a _
    ((measurable_anisotropicProcessPairResponse D μ q e).pow_const 2)

theorem anisotropicFreshTerminalPairLaw_spin_square (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i : Fin n) :
    (∫z,Paper.spinSign (z.2.1 i)*Paper.spinSign (z.2.2 i)
        ∂anisotropicFreshTerminalPairLaw D μ a q)=
      ∫p,(anisotropicProcessSpinResponse D μ q i p)^2∂anisotropicMeasureSampleLaw D μ a := by
  rw [fresh_pair_integral D μ a q (fun σ=>Paper.spinSign (σ i))]
  have hk:=(anisotropicFreshTerminalSpinKernel_conditional_mean D μ a q
    (fun σ=>Paper.spinSign (σ i))).symm.trans
      (anisotropicMeasureSpinPathLaw_spin_condExp D μ a q i)
  have hs : (fun p=>(∫σ,Paper.spinSign (σ i)∂anisotropicFreshTerminalSpinKernel D μ a q p)^2)
      =ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      (fun p=>(anisotropicProcessSpinResponse D μ q i p.1)^2) := by
    filter_upwards [hk] with p hp using congrArg (fun x : ℝ=>x^2) hp
  rw [integral_congr_ae hs]
  exact integral_anisotropicMeasureSpinPathLaw_sample D μ a _
    ((measurable_anisotropicProcessSpinResponse D μ q i).pow_const 2)

end QuantitativeFollowup
