module
public import FourPapersCommon.FiniteStateCascadeLinearTransport
public import FourPapersCommon.FiniteStateCascadeOrder
public import FourPapersCommon.FiniteGaussianBlockLaw
public import OverlapPaper.ReplicaSourceTensorTilt
public import OverlapPaper.ReplicaSourceGroupBaseline

@[expose] public section

/-! Linear site projections and the exact lifted independent-site Gaussian
cascade. These definitions retain all sites and all replica coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal
namespace FourPapersCommon
variable {B R I : Type*} [Fintype B] [Fintype R] [Fintype I]

 def finiteGaussianSiteProjection (i : B) :
    FiniteStateField (B×R) →L[ℝ] FiniteStateField R :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun r => x (i,r))
      map_add' := by intro x y; ext r; simp
      map_smul' := by intro c x; ext r; simp }

 @[simp] theorem finiteGaussianSiteProjection_apply (i : B) (x : FiniteStateField (B×R)) (r : R) :
    finiteGaussianSiteProjection i x r=x (i,r) := rfl

 def finiteGaussianSiteLift (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField R) :
    FiniteStateGaussianInput (B×I) →L[ℝ] FiniteStateField (B×R) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun p => L (finiteGaussianSiteProjection p.1 z) p.2)
      map_add' := by intro x y; ext p; simp
      map_smul' := by intro c x; ext p; simp }

 @[simp] theorem finiteGaussianSiteLift_apply
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField R)
    (z : FiniteStateGaussianInput (B×I)) (i : B) (r : R) :
    finiteGaussianSiteLift L z (i,r)=L (finiteGaussianSiteProjection i z) r := rfl

 @[simp] theorem finiteGaussianSiteProjection_lift (i : B)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField R)
    (z : FiniteStateGaussianInput (B×I)) :
    finiteGaussianSiteProjection i (finiteGaussianSiteLift L z)=L (finiteGaussianSiteProjection i z) := by
  ext r
  rfl

 def finiteGaussianSiteSum (F : FiniteStateField R → ℝ) (H : FiniteStateField (B×R)) : ℝ :=
  ∑ i : B, F (finiteGaussianSiteProjection i H)

 theorem finiteGaussianSiteSum_lipschitz (F : FiniteStateField R → ℝ) {C : ℝ≥0}
    (hF : LipschitzWith C F) :
    LipschitzWith (∑ i : B, C*‖finiteGaussianSiteProjection (R := R) i‖₊) (finiteGaussianSiteSum (B := B) F) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro H K
  rw [Real.dist_eq]
  unfold finiteGaussianSiteSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : B, |F (finiteGaussianSiteProjection i H)-F (finiteGaussianSiteProjection i K)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : B, (C : ℝ)*‖finiteGaussianSiteProjection (R := R) i‖*dist H K := by
      apply Finset.sum_le_sum
      intro i _
      have hh := (hF.comp (finiteGaussianSiteProjection (R := R) i).lipschitz).dist_le_mul H K
      simpa only [Function.comp_def, Real.dist_eq, NNReal.coe_mul, coe_nnnorm] using hh
    _ = _ := by rw [NNReal.coe_sum,Finset.sum_mul]; simp only [NNReal.coe_mul,coe_nnnorm]

 theorem finiteStateGaussianStep_site_sum (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField R)
    (F : FiniteStateField R → ℝ) {C : ℝ≥0} (hF : LipschitzWith C F)
    (H : FiniteStateField (B×R)) :
    finiteStateGaussianStep a (finiteGaussianSiteLift (B := B) L) (finiteGaussianSiteSum F) H =
      ∑ i : B, finiteStateGaussianStep a L F (finiteGaussianSiteProjection i H) := by
  classical
  let g := fun w : B → FiniteStateGaussianInput I =>
    ∑ i : B, F (finiteGaussianSiteProjection i H+L (w i))
  have hgm : Measurable g := (continuous_finsetSum _ (fun i _ => hF.continuous.comp
    (continuous_const.add (L.continuous.comp (continuous_apply i))))).measurable
  have hh := OverlapPaper.sourceLogAverage_map (stdGaussian (FiniteStateGaussianInput (B×I)))
    gaussianBlockCurry (measurable_gaussianBlockCurry (J := B) (I := I)) a g hgm
  rw [stdGaussian_map_gaussianBlockCurry] at hh
  have he : (fun z : FiniteStateGaussianInput (B×I) =>
      finiteGaussianSiteSum F (H+finiteGaussianSiteLift L z)) = fun z => g (gaussianBlockCurry z) := by
    funext z
    unfold finiteGaussianSiteSum g
    apply Finset.sum_congr rfl
    intro i _
    rw [map_add,finiteGaussianSiteProjection_lift]
    rfl
  unfold finiteStateGaussianStep
  rw [he,← hh]
  exact OverlapPaper.sourceLogAverage_pi_sum (fun _ : B => stdGaussian (FiniteStateGaussianInput I)) a
    (fun i z => F (finiteGaussianSiteProjection i H+L z))
    (fun i => (hF.continuous.comp (continuous_const.add L.continuous)).measurable)
    (fun i => integrable_finiteStateGaussian_lipschitz F hF L _)
    (fun i => integrable_exp_finiteStateGaussian_lipschitz F hF L _ a)

 theorem finiteStateGaussianCascade_site_sum (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField R)
    (F : FiniteStateField R → ℝ) {C : ℝ≥0} (hF : LipschitzWith C F)
    (J : ℕ) (H : FiniteStateField (B×R)) :
    finiteStateGaussianCascade a (fun j => finiteGaussianSiteLift (B := B) (L j))
      (finiteGaussianSiteSum F) J H =
      ∑ i : B, finiteStateGaussianCascade a L F J (finiteGaussianSiteProjection i H) := by
  induction J generalizing H with
  | zero => rfl
  | succ J ih =>
    have he : finiteStateGaussianCascade a (fun j => finiteGaussianSiteLift (B := B) (L j))
        (finiteGaussianSiteSum F) J = finiteGaussianSiteSum (finiteStateGaussianCascade a L F J) := funext ih
    rw [finiteStateGaussianCascade,he,finiteStateGaussianStep_site_sum (a J) (L J) _
      (finiteStateGaussianCascade_lipschitz F hF a ha L J)]
    rfl

end FourPapersCommon
