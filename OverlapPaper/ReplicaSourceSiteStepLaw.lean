module
public import OverlapPaper.ReplicaSourceSiteBaselineStep
public import FourPapersCommon.FiniteStateCascadeGibbsTransport

@[expose] public section

/-! The actual copied Gaussian site tilt is precisely the product of scalar
Parisi transitions, followed by copying within groups. External field shifts,
zero masses and zero variances are included in the measure identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal
namespace OverlapPaper
open FourPapersCommon SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
variable {d g : ℕ}

 theorem tilted_add_const_eq {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f : A → ℝ) (C : ℝ) :
    μ.tilted (fun y => f y+C)=μ.tilted f := by
  unfold Measure.tilted
  simp_rw [Real.exp_add]
  rw [integral_mul_const]
  congr 1
  funext y
  rw [mul_div_mul_right _ _ (Real.exp_ne_zero C)]

 def replicaSiteAbsoluteField (h : ℝ) (y : FiniteStateField (Fin d)) : Fin d → ℝ := fun l => h+y l

 theorem measurable_replicaSiteAbsoluteField (h : ℝ) :
    Measurable (replicaSiteAbsoluteField (d := d) h) := by
  unfold replicaSiteAbsoluteField
  fun_prop

 theorem replicaSiteCopyGaussian_absolute_raw_law (v : ℝ) (hv : 0≤v)
    (groupOf : Fin d → Fin g) (rep : Fin g → Fin d)
    (h : ℝ) (H : FiniteStateField (Fin d)) (hH : ∀ l, H l=H (rep (groupOf l))) :
    (finiteStateGaussianRawKernel (replicaSiteCopyGaussianCLM v groupOf) H).map (replicaSiteAbsoluteField h)=
      (Measure.pi (fun j => gaussianReal (h+H (rep j)) v.toNNReal)).map (replicaGroupCopy groupOf) := by
  let W : FiniteStateField (Fin d) := WithLp.toLp 2 (fun _ => h)
  let sh : FiniteStateField (Fin d) → Fin d → ℝ := WithLp.ofLp
  have hsh : Measurable sh := (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).measurable
  have hl := replicaSiteCopyGaussian_raw_law v hv groupOf rep (H+W)
    (fun l => by simp only [WithLp.ofLp_add,Pi.add_apply,W]; rw [hH l])
  have he : (fun z => replicaSiteAbsoluteField h (H+replicaSiteCopyGaussianCLM v groupOf z))=
      sh ∘ (fun z => (H+W)+replicaSiteCopyGaussianCLM v groupOf z) := by
    funext z
    ext l
    simp only [replicaSiteAbsoluteField,sh,Function.comp_def,WithLp.ofLp_add,Pi.add_apply,W]
    ring
  rw [finiteStateGaussianRawKernel_apply,Measure.map_map (measurable_replicaSiteAbsoluteField h) (by fun_prop)]
  change (stdGaussian (FiniteStateGaussianInput (Fin g))).map
    (fun z => replicaSiteAbsoluteField h (H+replicaSiteCopyGaussianCLM v groupOf z))=_
  have hmcopy : Measurable (fun y : Fin g → ℝ => WithLp.toLp 2 (replicaGroupCopy groupOf y)) := by
    simpa only [Function.comp_def] using
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp (measurable_replicaGroupCopy groupOf)
  rw [he,←Measure.map_map hsh (by fun_prop),hl,Measure.map_map hsh hmcopy]
  simp only [sh,Function.comp_def,WithLp.ofLp_toLp,WithLp.ofLp_add,Pi.add_apply,W,add_comm]

 theorem mixed_replica_site_baseline_stepLaw {k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (p : ℕ) (hp : p≤k+1)
    (groupOf : Fin d → Fin g) (rep : Fin g → Fin d)
    (hrep : ∀ j, groupOf (rep j)=j) (c : ℕ) (hc : 0<c)
    (hcard : ∀ j, (Finset.univ.filter (fun l => groupOf l=j)).card=c)
    (h : ℝ) (H : FiniteStateField (Fin d)) (hH : ∀ l, H l=H (rep (groupOf l)))
    (C : ℝ) (F : FiniteStateField (Fin d) → ℝ) (hF : Measurable F)
    (hbaseline : ∀ y, (∀ l, y l=y (rep (groupOf l))) →
      F y=(∑ l : Fin d, mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p+1),h+y l))+C) :
    (finiteStateGaussianStepLaw (s.m p/c)
      (replicaSiteCopyGaussianCLM (ξ.first (s.q (p+1))-ξ.first (s.q p)) groupOf) F H).map
      (replicaSiteAbsoluteField h)=
      replicaGroupKernel (mixedSchemeScalarStep ξ s p) groupOf rep (replicaSiteAbsoluteField h H) := by
  classical
  let v := ξ.first (s.q (p+1))-ξ.first (s.q p)
  have hv : 0≤v := sub_nonneg.mpr (ξ.first_strictMonoOn.monotoneOn
    ⟨by linarith [s.q_nonneg (show p≤k+2 by omega)],s.q_le_one (by omega)⟩
    ⟨by linarith [s.q_nonneg (show p+1≤k+2 by omega)],s.q_le_one (by omega)⟩ (s.q_mono p hp))
  let G : (Fin d → ℝ) → ℝ := fun y => (s.m p/c)*F (WithLp.toLp 2 (fun l => y l-h))
  have hG : Measurable G := (hF.comp ((PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp
    (by fun_prop : Measurable (fun y : Fin d → ℝ => fun l => y l-h)))).const_mul _
  have he : (fun y => G (replicaSiteAbsoluteField h y))=(fun y => (s.m p/c)*F y) := by
    funext y
    have hinv : (WithLp.toLp 2 (fun l => replicaSiteAbsoluteField h y l-h) : FiniteStateField (Fin d))=y := by
      ext l
      simp [replicaSiteAbsoluteField]
    dsimp [G]
    rw [hinv]
  change ((finiteStateGaussianRawKernel (replicaSiteCopyGaussianCLM v groupOf) H).tilted
    (fun y => (s.m p/c)*F y)).map (replicaSiteAbsoluteField h)=_
  rw [←he,←tilted_map_eq _ _ (measurable_replicaSiteAbsoluteField h) G hG,
    replicaSiteCopyGaussian_absolute_raw_law v hv groupOf rep h H hH,
    tilted_map_eq _ _ (measurable_replicaGroupCopy groupOf) G hG]
  have hcR : (c : ℝ)≠0 := by exact_mod_cast hc.ne'
  have hf (y : Fin g → ℝ) : G (replicaGroupCopy groupOf y)=
      (∑ j : Fin g, s.m p*mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p+1),y j))+(s.m p/c)*C := by
    have hconst (l : Fin d) : (WithLp.toLp 2 (fun l => replicaGroupCopy groupOf y l-h) : FiniteStateField (Fin d)) l=
        (WithLp.toLp 2 (fun l => replicaGroupCopy groupOf y l-h) : FiniteStateField (Fin d)) (rep (groupOf l)) := by
      simp only [WithLp.ofLp_toLp,replicaGroupCopy,hrep]
    dsimp [G]
    rw [hbaseline _ hconst]
    have hsum := replica_group_sum_of_constant groupOf rep c hcard
      (fun l => mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p+1),replicaGroupCopy groupOf y l))
      (fun l => by simp only [replicaGroupCopy,hrep])
    simp only [WithLp.ofLp_toLp] at *
    simp_rw [show ∀ x : ℝ, h+(x-h)=x by intro x; ring]
    rw [mul_add,hsum]
    simp only [replicaGroupCopy,hrep,←mul_assoc,div_mul_cancel₀ _ hcR,Finset.mul_sum]
  simp_rw [hf]
  rw [tilted_add_const_eq]
  have hb := mixed_replica_group_baseline_tilt ξ s p hp groupOf rep hrep (replicaSiteAbsoluteField h H)
  rw [tilted_map_eq _ _ (measurable_replicaGroupCopy groupOf) _ (by
    exact Finset.measurable_fun_sum Finset.univ (fun j _ =>
      ((continuous_mixedPotential_section ξ _ _).measurable.comp (measurable_pi_apply _)).const_mul _))] at hb
  simp only [replicaGroupCopy,hrep,replicaSiteAbsoluteField] at hb
  exact hb

end OverlapPaper
