module
public import QuantitativeFollowup.AnisotropicRecordedMovingKernelConvergence

@[expose] public section

/-! Actual normalized full recorded-law convergence with moving observation
levels, including atoms and repeated levels. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped NNReal Topology BoundedContinuousFunction
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem tendsto_anisotropicRecordedProfileProbability_moving_schedule {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure} (hμ : Tendsto μ l (𝓝 ν))
    (a : ℝ) (q : L→ℕ→Paper.Overlap) (Q : ℕ→Paper.Overlap)
    {J : ℕ} (T : FiniteTerminalGenealogy J)
    (hq : ∀p,p≤J→Tendsto (fun j=>q j p) l (𝓝 (Q p)))
    (hmono : ∀j,∀p,p<J→q j (p+1)≤q j p) (hMono : ∀p,p<J→Q (p+1)≤Q p) :
    Tendsto (fun j=>anisotropicRecordedProfileProbability D (μ j) a (q j) T) l
      (𝓝 (anisotropicRecordedProfileProbability D ν a Q T)) := by
  haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
  haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
  haveI : PseudoMetrizableSpace (Records (AnisotropicObservationState n) (Configuration n) T):=inferInstance
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let G:=fun j g=>anisotropicMeasureOuterWeight D (μ j) a g*
    (∫v,f v ∂(anisotropicRecordedProfileJointProbability D (μ j) (q j) T (g,0):Measure _))
  let F:=fun g=>anisotropicMeasureOuterWeight D ν a g*
    (∫v,f v ∂(anisotropicRecordedProfileJointProbability D ν Q T (g,0):Measure _))
  let B:=fun g=>2*anisotropicOuterExponentialEnvelope D ν a g/anisotropicMeasureOuterPartition D ν a*‖f‖
  have hm (j : L) : AEStronglyMeasurable (G j) (anisotropicDisorderLaw n) := by
    have hmean : Measurable (fun g : AnisotropicDisorder n=>
        ∫v,f v ∂(anisotropicRecordedProfileJointProbability D (μ j) (q j) T (g,0):Measure _)) :=
      (measurable_anisotropicRecordedProfileJointMean D (μ j) (q j) T f).comp
        (measurable_id.prodMk measurable_const)
    exact ((measurable_anisotropicMeasureOuterWeight D (μ j) a).mul hmean).aestronglyMeasurable
  have hb : ∀ᶠj in l,∀ᵐg∂anisotropicDisorderLaw n,‖G j g‖≤B g := by
    filter_upwards [anisotropicMeasureOuterWeight_profile_eventual_bound D hμ a] with j hj
    exact .of_forall fun g=>by
      have hi : ‖∫v,f v ∂(anisotropicRecordedProfileJointProbability D (μ j) (q j) T (g,0):Measure _)‖≤‖f‖ := by
        simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
          (μ:=(anisotropicRecordedProfileJointProbability D (μ j) (q j) T (g,0):Measure _))
          (.of_forall f.norm_coe_le_norm)
      exact (norm_mul _ _).trans_le (mul_le_mul (hj g) hi (norm_nonneg _)
        (by unfold anisotropicOuterExponentialEnvelope
            positivity [anisotropicMeasureOuterPartition_pos D ν a]))
  have hB : Integrable B (anisotropicDisorderLaw n):=
    ((integrable_anisotropicOuterExponentialEnvelope D ν a).const_mul 2 |>.div_const _).mul_const ‖f‖
  have hp (g : AnisotropicDisorder n) : Tendsto (fun j=>G j g) l (𝓝 (F g)) := by
    have ht:=tendsto_anisotropicRecordedProfileTreeProbability_moving_schedule D hμ q Q T hq hmono hMono g (tendsto_const_nhds (x:=(0:Field n)))
    have hj : Tendsto (fun j=>anisotropicRecordedProfileJointProbability D (μ j) (q j) T (g,0)) l
        (𝓝 (anisotropicRecordedProfileJointProbability D ν Q T (g,0))) :=
      ProbabilityMeasure.continuous_prod.tendsto _ |>.comp (tendsto_const_nhds.prodMk_nhds ht)
    exact (tendsto_anisotropicMeasureOuterWeight_profile D hμ a g).mul
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hj f)
  have ht:=tendsto_integral_filter_of_dominated_convergence B (.of_forall hm) hb hB (.of_forall hp)
  have he : (fun j:L=>∫v,f v ∂(anisotropicRecordedProfileProbability D (μ j) a (q j) T:Measure _))=
      (fun j=>∫g,G j g ∂anisotropicDisorderLaw n) := by
    funext j
    exact integral_anisotropicRecordedProfileProbability_weighted D (μ j) a (q j) T f
  rw [he,integral_anisotropicRecordedProfileProbability_weighted D ν a Q T f]
  exact ht

end QuantitativeFollowup
