module
public import QuantitativeFollowup.AnisotropicObservationRestartIdentities
public import QuantitativeFollowup.AnisotropicRecordedProfileTree
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

@[expose] public section

/-! The genuine native restart kernel composes at every deterministic
observation time, for every disorder and current field. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 850000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem anisotropicObservationTransition_canonical_mean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r)
    (g : AnisotropicDisorder n) (x : Field n) (F : AnisotropicObservationState n→ℝ)
    (hF : Measurable F) :
    (∫z,F z∂anisotropicObservationTransition D μ q r (g,x))=
      ∫p,F (g,vectorAdditiveState (anisotropicRestartDriftData D μ g q) 1 x 1
        ((r:ℝ)-(q:ℝ)).toNNReal p) ∂vectorDisorderBrownianMeasure n := by
  let H : VectorWienerPath n→ℝ:=fun W=>F (g,anisotropicRestartNoiseStatePath D μ q ((g,x),W)
    ((r:ℝ)-(q:ℝ)))
  have hN : Measurable (fun W=>anisotropicObservationNoiseAdvance D μ q r ((g,x),W)) :=
    (measurable_anisotropicObservationNoiseAdvance D μ q r).comp
      (measurable_const.prodMk measurable_id)
  have hH : Measurable H:=hF.comp hN
  have hc : HasLaw (fun p : VectorDisorderBrownianSample n=>vectorCanonicalBrownianPath p.2)
      (vectorWienerMeasure n) (vectorDisorderBrownianMeasure n) :=
    hasLaw_vectorCanonicalBrownianPath.comp (hasLaw_vectorBrownian_samples_with_disorder n)
  rw [anisotropicObservationTransition_apply]
  have hmap:=integral_map (μ:=vectorWienerMeasure n)
    (φ:=fun W=>anisotropicObservationNoiseAdvance D μ q r ((g,x),W)) (f:=F)
    hN.aemeasurable hF.aestronglyMeasurable
  refine hmap.trans ?_
  change (∫W,H W∂vectorWienerMeasure n)=_
  rw [←hc.integral_comp hH.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun p=>by
    have ht : (((r:ℝ)-(q:ℝ)).toNNReal:ℝ)=(r:ℝ)-(q:ℝ) :=
      Real.coe_toNNReal _ (sub_nonneg.mpr hqr)
    dsimp only [H,Function.comp_def]
    have he:=anisotropicRestartNoiseStatePath_canonical_extended D μ g q x p
      ((r:ℝ)-(q:ℝ)).toNNReal (by rw [ht];linarith [r.property.2])
    rw [ht] at he
    exact congrArg (fun y=>F (g,y)) he

theorem anisotropicObservationTransition_semigroup_mean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r s : Paper.Overlap) (hqr : q ≤ r) (hrs : r ≤ s)
    (g : AnisotropicDisorder n) (x : Field n) (F : AnisotropicObservationState n→ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀z,‖F z‖≤C) :
    (∫z,F z∂anisotropicObservationTransition D μ q s (g,x))=
      ∫z,(∫y,F y∂anisotropicObservationTransition D μ r s z)
        ∂anisotropicObservationTransition D μ q r (g,x) := by
  let u : Paper.Overlap:=⟨(r:ℝ)-(q:ℝ),⟨sub_nonneg.mpr hqr,by linarith [r.property.2,q.property.1]⟩⟩
  let v : ℝ≥0:=((s:ℝ)-(r:ℝ)).toNNReal
  have hvcoe : (v:ℝ)=(s:ℝ)-(r:ℝ):=Real.coe_toNNReal _ (sub_nonneg.mpr hrs)
  have hv : v≤vectorRestartHorizon u := by
    rw [←NNReal.coe_le_coe,vectorRestartHorizon,
      Real.coe_toNNReal _ (sub_nonneg.mpr u.property.2),hvcoe]
    change (s:ℝ)-(r:ℝ)≤1-((r:ℝ)-(q:ℝ))
    linarith [s.property.2,q.property.1]
  have htime : (u:ℝ).toNNReal+v=((s:ℝ)-(q:ℝ)).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal _ u.property.1,hvcoe,
      Real.coe_toNNReal _ (sub_nonneg.mpr (hqr.trans hrs))]
    change (r:ℝ)-(q:ℝ)+((s:ℝ)-(r:ℝ))=(s:ℝ)-(q:ℝ)
    ring
  let d:=anisotropicRestartDriftData D μ g q
  let G : AnisotropicObservationState n→ℝ:=
    fun z=>∫y,F y∂anisotropicObservationTransition D μ r s z
  have hG : Measurable G:=hF.stronglyMeasurable.integral_kernel.measurable
  rw [anisotropicObservationTransition_canonical_mean D μ q s (hqr.trans hrs) g x F hF,
    anisotropicObservationTransition_canonical_mean D μ q r hqr g x G hG]
  have hh:=condExp_vectorAdditiveState_future d 1 x u v hv
    (fun z=>F (g,z.2)) (hF.comp (measurable_const.prodMk measurable_snd)) C (fun z=>hC _)
  rw [htime] at hh
  have hright : (fun p : VectorDisorderBrownianSample n=>∫W,F (g,
      vectorNoiseRestartStatePath d 1 u ((p.1,vectorAdditiveState d 1 x 1 (u:ℝ).toNNReal p),W) v)
        ∂vectorWienerMeasure n)=
      fun p=>G (g,vectorAdditiveState d 1 x 1 ((r:ℝ)-(q:ℝ)).toNNReal p) := by
    funext p
    change _=∫z,F z∂anisotropicObservationTransition D μ r s
      (g,vectorAdditiveState d 1 x 1 (u:ℝ).toNNReal p)
    rw [anisotropicObservationTransition_apply]
    have hm : Measurable (fun W=>anisotropicObservationNoiseAdvance D μ r s
        ((g,vectorAdditiveState d 1 x 1 (u:ℝ).toNNReal p),W)) :=
      (measurable_anisotropicObservationNoiseAdvance D μ r s).comp (measurable_const.prodMk measurable_id)
    refine Eq.trans ?_ (integral_map (μ:=vectorWienerMeasure n)
      (φ:=fun W=>anisotropicObservationNoiseAdvance D μ r s
        ((g,vectorAdditiveState d 1 x 1 (u:ℝ).toNNReal p),W)) (f:=F)
      hm.aemeasurable hF.aestronglyMeasurable).symm
    apply integral_congr_ae
    exact .of_forall fun W=>by
      have he:=anisotropicRestartNoiseStatePath_shift D μ g q r u rfl p.1
        (vectorAdditiveState d 1 x 1 (u:ℝ).toNNReal p) W v (by rw [hvcoe];linarith [s.property.2])
      exact congrArg (fun z=>F (g,z)) (he.trans (congrArg
        (anisotropicRestartNoiseStatePath D μ r ((g,vectorAdditiveState d 1 x 1 (u:ℝ).toNNReal p),W)) hvcoe))
  change _=ᵐ[_] (fun p : VectorDisorderBrownianSample n=>∫W,F (g,
      vectorNoiseRestartStatePath d 1 u ((p.1,vectorAdditiveState d 1 x 1 (u:ℝ).toNNReal p),W) v)
        ∂vectorWienerMeasure n) at hh
  rw [hright] at hh
  have hi:=integral_congr_ae hh
  rw [integral_condExp ((vectorBrownianFiltration n).le _)] at hi
  exact hi

theorem anisotropicObservationTransition_semigroup (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r s : Paper.Overlap) (hqr : q ≤ r) (hrs : r ≤ s) :
    (anisotropicObservationTransition D μ r s) ∘ₖ (anisotropicObservationTransition D μ q r)=
      anisotropicObservationTransition D μ q s := by
  ext z : 1
  rcases z with ⟨g,x⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [Kernel.integral_comp (f.integrable _)]
  exact (anisotropicObservationTransition_semigroup_mean D μ q r s hqr hrs g x f
    f.continuous.measurable ‖f‖ f.norm_coe_le_norm).symm

theorem anisotropicObservationTransition_same_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    anisotropicObservationTransition D μ q q=Kernel.id := by
  ext z : 1
  rcases z with ⟨g,x⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [anisotropicObservationTransition_canonical_mean D μ q q le_rfl g x f f.continuous.measurable]
  simp only [sub_self,Real.toNNReal_zero,vectorAdditiveState_zero]
  simp [Kernel.id_apply]

end QuantitativeFollowup
