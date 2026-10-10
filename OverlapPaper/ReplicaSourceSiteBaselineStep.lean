module
public import OverlapPaper.ReplicaSourceSiteGaussianLaw

@[expose] public section

/-! Exact scalar baseline of a genuinely sampled grouped Gaussian site step.
The group-size normalization is derived from the literal fiber cardinality. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal
namespace OverlapPaper
open FourPapersCommon SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1200000
variable {d g : ℕ}

 theorem sourceLogAverage_add_const {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (a : ℝ) (F : A → ℝ) (C : ℝ)
    (hi : Integrable F ν) (he : Integrable (fun x => Real.exp (a*F x)) ν) :
    sourceLogAverage ν a (fun x => F x+C)=sourceLogAverage ν a F+C := by
  by_cases ha : a=0
  · simp only [sourceLogAverage,ha,ite_true]
    rw [integral_add hi (integrable_const C)]
    simp
  · simp only [sourceLogAverage,ha,ite_false]
    simp_rw [mul_add,Real.exp_add]
    rw [integral_mul_const,Real.log_mul (integral_exp_pos he).ne' (Real.exp_ne_zero _),Real.log_exp]
    field_simp

 theorem replica_group_sum_of_constant (groupOf : Fin d → Fin g)
    (representative : Fin g → Fin d) (c : ℕ)
    (hcard : ∀ j, (Finset.univ.filter (fun l => groupOf l=j)).card=c)
    (f : Fin d → ℝ) (hf : ∀ l, f l=f (representative (groupOf l))) :
    (∑ l : Fin d, f l)=(c : ℝ)*∑ j : Fin g, f (representative j) := by
  classical
  rw [←Finset.sum_fiberwise (Finset.univ : Finset (Fin d)) groupOf f]
  have he (j : Fin g) : (∑ l ∈ Finset.univ.filter (fun l => groupOf l=j), f l)=
      (c : ℝ)*f (representative j) := by
    have hh : (∑ l ∈ Finset.univ.filter (fun l => groupOf l=j), f l)=
        ∑ _l ∈ Finset.univ.filter (fun l => groupOf l=j), f (representative j) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [hf l,(Finset.mem_filter.mp hl).2]
    rw [hh,Finset.sum_const,hcard j,nsmul_eq_mul]
  simp_rw [he]
  rw [Finset.mul_sum]

 theorem replicaSiteCopyGaussianStep_eq_group_logAverage (v : ℝ) (hv : 0 ≤ v)
    (groupOf : Fin d → Fin g) (representative : Fin g → Fin d)
    (H : FiniteStateField (Fin d)) (hH : ∀ l, H l=H (representative (groupOf l)))
    (a : ℝ) (F : FiniteStateField (Fin d) → ℝ) (hF : Measurable F) :
    finiteStateGaussianStep a (replicaSiteCopyGaussianCLM v groupOf) F H=
      sourceLogAverage
        ((Measure.pi (fun j => gaussianReal (H (representative j)) v.toNNReal)).map (replicaGroupCopy groupOf))
        a (fun y => F (WithLp.toLp 2 y)) := by
  have hm : Measurable (fun z : FiniteStateGaussianInput (Fin g) => H+replicaSiteCopyGaussianCLM v groupOf z) := by fun_prop
  have hh := sourceLogAverage_map (stdGaussian (FiniteStateGaussianInput (Fin g))) _ hm a F hF
  rw [replicaSiteCopyGaussian_raw_law v hv groupOf representative H hH] at hh
  have hh' := sourceLogAverage_map
    (Measure.pi (fun j => gaussianReal (H (representative j)) v.toNNReal))
    (fun y => WithLp.toLp 2 (replicaGroupCopy groupOf y))
    ((PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp (measurable_replicaGroupCopy groupOf)) a F hF
  have hh'' := sourceLogAverage_map
    (Measure.pi (fun j => gaussianReal (H (representative j)) v.toNNReal))
    (replicaGroupCopy groupOf) (measurable_replicaGroupCopy groupOf) a
    (fun y => F (WithLp.toLp 2 y)) (hF.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable)
  rw [hh'] at hh
  exact hh.symm.trans hh''.symm

 theorem mixed_replica_site_baseline_step {k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (p : ℕ) (hp : p≤k+1)
    (groupOf : Fin d → Fin g) (representative : Fin g → Fin d)
    (hrep : ∀ j, groupOf (representative j)=j) (c : ℕ) (hc : 0<c)
    (hcard : ∀ j, (Finset.univ.filter (fun l => groupOf l=j)).card=c)
    (H : FiniteStateField (Fin d)) (hH : ∀ l, H l=H (representative (groupOf l)))
    (C : ℝ) (F : FiniteStateField (Fin d) → ℝ) (hF : Measurable F)
    (hbaseline : ∀ y, (∀ l, y l=y (representative (groupOf l))) →
      F y=(∑ l : Fin d, mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p+1),y l))+C) :
    finiteStateGaussianStep (s.m p/c)
      (replicaSiteCopyGaussianCLM (ξ.first (s.q (p+1))-ξ.first (s.q p)) groupOf) F H=
      (∑ l : Fin d, mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q p,H l))+C := by
  classical
  let v := ξ.first (s.q (p+1))-ξ.first (s.q p)
  have hv : 0≤v := sub_nonneg.mpr (ξ.first_strictMonoOn.monotoneOn ⟨(by linarith [s.q_nonneg (show p≤k+2 by omega)]),s.q_le_one (by omega)⟩
    ⟨(by linarith [s.q_nonneg (show p+1≤k+2 by omega)]),s.q_le_one (by omega)⟩ (s.q_mono p hp))
  let G := fun y : FiniteStateField (Fin d) =>
    (c : ℝ)*∑ j : Fin g, mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p+1),y (representative j))
  have he : finiteStateGaussianStep (s.m p/c) (replicaSiteCopyGaussianCLM v groupOf) F H=
      finiteStateGaussianStep (s.m p/c) (replicaSiteCopyGaussianCLM v groupOf) (fun y => G y+C) H := by
    unfold finiteStateGaussianStep
    congr 1
    funext z
    have hz (l : Fin d) : (H+replicaSiteCopyGaussianCLM v groupOf z) l=
        (H+replicaSiteCopyGaussianCLM v groupOf z) (representative (groupOf l)) := by
      simp only [WithLp.ofLp_add,Pi.add_apply,replicaSiteCopyGaussianCLM_apply,hH l,hrep]
    rw [hbaseline _ hz]
    congr 1
    exact replica_group_sum_of_constant groupOf representative c hcard _ (fun l => congrArg
      (fun x => mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p+1),x)) (hz l))
  rw [he,replicaSiteCopyGaussianStep_eq_group_logAverage v hv groupOf representative H hH]
  · let ν := (Measure.pi (fun j => gaussianReal (H (representative j)) v.toNNReal)).map (replicaGroupCopy groupOf)
    let fg := fun y : Fin d → ℝ => (c : ℝ)*∑ j : Fin g,
      mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p+1),y (representative j))
    have hmc := continuous_mixedPotential_section ξ (Paper.parisiSchemeMeasure s) (s.q (p+1))
    have hg : Measurable fg :=
      (Finset.measurable_fun_sum Finset.univ (fun j _ => hmc.measurable.comp (measurable_pi_apply _))).const_mul c
    have hcR : (c : ℝ)≠0 := by exact_mod_cast hc.ne'
    have hl := mixed_replica_group_baseline_step ξ s p hp groupOf representative hrep (c : ℝ) hcR
      (fun l => H l)
    have hequal : (fun y : Fin d → ℝ => (fun y : FiniteStateField (Fin d) => G y+C) (WithLp.toLp 2 y))=
        fun y => fg y+C := rfl
    rw [hequal]
    -- Both integrability assertions are genuine finite Gaussian linear-growth integrals.
    have hgrowth := mixedPotential_hasLinearGrowth ξ (Paper.parisiSchemeMeasure s)
      (show s.q (p+1)∈Icc (0 : ℝ) 1 from ⟨s.q_nonneg (by omega),s.q_le_one (by omega)⟩)
    have hi : Integrable fg ν := by
      rw [show ν=(Measure.pi (fun j => gaussianReal (H (representative j)) v.toNNReal)).map (replicaGroupCopy groupOf) from rfl]
      apply (integrable_map_measure hg.aestronglyMeasurable
        (measurable_replicaGroupCopy groupOf).aemeasurable).mpr
      have he' : (fun x : Fin g → ℝ => fg (replicaGroupCopy groupOf x))=
          fun x => (c : ℝ)*∑ j : Fin g, mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p+1),x j) := by
        simp only [fg,replicaGroupCopy,hrep]
      simp only [Function.comp_def]
      rw [he']
      exact (integrable_finsetSum Finset.univ (fun j _ =>
        (measurePreserving_eval _ j).hasLaw.integrable_comp
          (hgrowth.toHasExpGrowth.integrable_gaussianReal hmc.measurable.aestronglyMeasurable))).const_mul c
    have hie : Integrable (fun y => Real.exp ((s.m p/c)*fg y)) ν := by
      change Integrable _ ((Measure.pi (fun j => gaussianReal (H (representative j)) v.toNNReal)).map (replicaGroupCopy groupOf))
      apply (integrable_map_measure ((hg.const_mul _).exp.aestronglyMeasurable)
        (measurable_replicaGroupCopy groupOf).aemeasurable).mpr
      have he' : (fun x : Fin g → ℝ => Real.exp ((s.m p/c)*fg (replicaGroupCopy groupOf x)))=
          fun x => ∏ j : Fin g, Real.exp (s.m p*mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p+1),x j)) := by
        simp only [fg,replicaGroupCopy,hrep]
        simp only [←mul_assoc,div_mul_cancel₀ _ hcR,Finset.mul_sum,Real.exp_sum]
      simp only [Function.comp_def]
      rw [he']
      exact Integrable.fintype_prod (fun j => ((hgrowth.exp_mul (s.m p)).integrable_gaussianReal
        ((hmc.measurable.const_mul _).exp.aestronglyMeasurable)))
    rw [sourceLogAverage_add_const ν (s.m p/c) fg C hi hie,hl]
    congr 1
    exact (replica_group_sum_of_constant groupOf representative c hcard _
      (fun l => congrArg (fun x => mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q p,x)) (hH l))).symm
  · have hmc := continuous_mixedPotential_section ξ (Paper.parisiSchemeMeasure s) (s.q (p+1))
    exact ((Finset.measurable_fun_sum Finset.univ (fun j _ => hmc.measurable.comp
      ((measurable_pi_apply _).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).measurable))).const_mul c).add_const C

end OverlapPaper
