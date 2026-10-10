module
public import OverlapPaper.ReplicaSourceSiteFields
public import OverlapPaper.ReplicaSourceGroupBaseline
public import FourPapersCommon.FiniteStateGaussianLaw

@[expose] public section

/-! The literal copied site Gaussian field has exactly the independently
sampled group-Gaussian law, including zero variance and unused labels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal
namespace OverlapPaper
open FourPapersCommon
set_option maxHeartbeats 1000000
variable {d g b : ℕ}

 theorem replicaSiteCopyGaussian_spectral (v : ℝ) (hv : 0 ≤ v)
    (groupOf : Fin d → Fin g) (l j : Fin d) :
    finiteStateSpectralCovariance (replicaSiteCopyGaussianCLM v groupOf) l j =
      if groupOf l=groupOf j then v else 0 := by
  classical
  simp only [finiteStateSpectralCovariance,replicaSiteCopyGaussianCLM_apply,EuclideanSpace.single_apply]
  by_cases h : groupOf l=groupOf j
  · simp only [h,Pi.single_apply]
    simp only [mul_ite,ite_mul,mul_zero,zero_mul,mul_one,one_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    nlinarith [Real.sq_sqrt hv]
  · have he (i : Fin g) : Real.sqrt v*(if groupOf l=i then 1 else 0)*
        (Real.sqrt v*(if groupOf j=i then 1 else 0))=0 := by
      by_cases hl : groupOf l=i
      · have hj : groupOf j≠i := by intro hj; exact h (hl.trans hj.symm)
        simp [hl,hj]
      · simp [hl]
    simp_rw [he]
    simp [h]

 theorem replicaSiteCopyGaussian_step_eq_of_partition (v : ℝ) (hv : 0 ≤ v)
    (groupOf : Fin d → Fin g) (other : Fin d → Fin b)
    (hpart : ∀ l j, groupOf l=groupOf j ↔ other l=other j)
    (a : ℝ) (F : FiniteStateField (Fin d) → ℝ) (hF : Measurable F) (H : FiniteStateField (Fin d)) :
    finiteStateGaussianStep a (replicaSiteCopyGaussianCLM v groupOf) F H=
      finiteStateGaussianStep a (replicaSiteCopyGaussianCLM v other) F H := by
  apply finiteStateGaussianStep_eq_of_spectral_covariance _ _ _ a F hF H
  intro l j
  rw [replicaSiteCopyGaussian_spectral v hv groupOf,replicaSiteCopyGaussian_spectral v hv other]
  simp only [hpart l j]

 theorem gaussianReal_affine_sqrt_map (x v : ℝ) (hv : 0 ≤ v) :
    (gaussianReal 0 1).map (fun z => x+Real.sqrt v*z)=gaussianReal x v.toNNReal := by
  have he : (fun z : ℝ => x+Real.sqrt v*z)=(fun z : ℝ => x+z) ∘ (fun z => Real.sqrt v*z) := rfl
  rw [he,←Measure.map_map (by fun_prop) (by fun_prop),gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  congr 1
  · ring
  · apply Subtype.ext
    change (Real.sqrt v)^2*1=v.toNNReal
    rw [mul_one,Real.sq_sqrt hv,Real.coe_toNNReal v hv]

 theorem replicaSiteCopyGaussian_raw_law (v : ℝ) (hv : 0 ≤ v)
    (groupOf : Fin d → Fin g) (representative : Fin g → Fin d)
    (H : FiniteStateField (Fin d)) (hH : ∀ l, H l=H (representative (groupOf l))) :
    (stdGaussian (FiniteStateGaussianInput (Fin g))).map
      (fun z => H+replicaSiteCopyGaussianCLM v groupOf z) =
      (Measure.pi (fun j => gaussianReal (H (representative j)) v.toNNReal)).map
        (fun y => WithLp.toLp 2 (replicaGroupCopy groupOf y)) := by
  classical
  rw [←map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop)]
  let f := fun y : Fin g → ℝ => fun j => H (representative j)+Real.sqrt v*y j
  have he : (fun z : Fin g → ℝ => H+replicaSiteCopyGaussianCLM v groupOf (WithLp.toLp 2 z))=
      (fun y => WithLp.toLp 2 (replicaGroupCopy groupOf y)) ∘ f := by
    funext z
    ext l
    simp only [Function.comp_def,replicaSiteCopyGaussianCLM_apply,WithLp.ofLp_toLp,
      WithLp.ofLp_add,Pi.add_apply,replicaGroupCopy,f,hH l]
  simp only [Function.comp_def]
  have hcopy : Measurable (fun y : Fin g → ℝ => WithLp.toLp 2 (replicaGroupCopy groupOf y)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp (measurable_replicaGroupCopy groupOf)
  rw [he,←Measure.map_map hcopy (by dsimp [f]; fun_prop)]
  have hf : (Measure.pi (fun _ : Fin g => gaussianReal 0 1)).map f=
      Measure.pi (fun j => gaussianReal (H (representative j)) v.toNNReal) := by
    change (Measure.pi (fun _ : Fin g => gaussianReal 0 1)).map
      (fun y j => H (representative j)+Real.sqrt v*y j) = _
    rw [Measure.pi_map_pi (fun j => (by fun_prop : Measurable (fun z : ℝ => H (representative j)+Real.sqrt v*z)).aemeasurable)]
    congr 1
    funext j
    exact gaussianReal_affine_sqrt_map _ _ hv
  rw [hf]

end OverlapPaper
