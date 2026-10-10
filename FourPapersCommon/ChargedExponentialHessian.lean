module
public import FourPapersCommon.ExponentialDensityHessian

@[expose] public section

/-! The genuine Gaussian score of a linear energy minus finitely many
charged smooth potentials. No probability response is an input. -/
noncomputable section
open scoped ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {E H A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def chargedLogPotential (L : E→L[ℝ]ℝ) (cs : List (ℝ×A))
    (P : A→H→ℝ) (B : A→E→L[ℝ]H) (x : E) : ℝ :=
  L x-(cs.map (fun c=>c.1*P c.2 (B c.2 x))).sum

def chargedDirectionalScore (L : E→L[ℝ]ℝ) (cs : List (ℝ×A))
    (P : A→H→ℝ) (B : A→E→L[ℝ]H) (x v : E) : ℝ :=
  L v-(cs.map (fun c=>c.1*fderiv ℝ (P c.2) (B c.2 x) (B c.2 v))).sum

def chargedDirectionalCurvature (cs : List (ℝ×A))
    (P : A→H→ℝ) (B : A→E→L[ℝ]H) (x v : E) : ℝ :=
  (cs.map (fun c=>c.1*exponentialDensityHessian (P c.2) (B c.2 x)
    (B c.2 v) (B c.2 v))).sum

private theorem hasFDerivAt_weighted_list (cs : List (ℝ×A))
    (f : A→E→ℝ) (d : A→E→L[ℝ]ℝ) (x : E)
    (hf : ∀a,HasFDerivAt (f a) (d a) x) :
    HasFDerivAt (fun y=>(cs.map (fun c=>c.1*f c.2 y)).sum)
      ((cs.map (fun c=>c.1 • d c.2)).sum) x := by
  induction cs with
  | nil => exact hasFDerivAt_const 0 x
  | cons c cs ih =>
    convert! ((hf c.2).const_smul c.1).add ih using 1 <;>
      simp only [List.map_cons,List.sum_cons,Pi.add_apply,Pi.smul_apply,smul_eq_mul]

private theorem clm_list_apply (ds : List (E→L[ℝ]ℝ)) (v : E) :
    ds.sum v=(ds.map (fun D=>D v)).sum := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp only [List.map_cons,List.sum_cons,ContinuousLinearMap.add_apply,ih]

theorem fderiv_chargedLogPotential (L : E→L[ℝ]ℝ) (cs : List (ℝ×A))
    (P : A→H→ℝ) (B : A→E→L[ℝ]H) (hP : ∀a,ContDiff ℝ 2 (P a)) (x v : E) :
    fderiv ℝ (chargedLogPotential L cs P B) x v=chargedDirectionalScore L cs P B x v := by
  have hd:=hasFDerivAt_weighted_list cs (fun a y=>P a (B a y))
    (fun a=>(fderiv ℝ (P a) (B a x)).comp (B a)) x
    (fun a=>((hP a).differentiable (by norm_num) (B a x)).hasFDerivAt.comp x (B a).hasFDerivAt)
  have hh:=L.hasFDerivAt.sub hd
  have hh' : HasFDerivAt (chargedLogPotential L cs P B)
      (L-(cs.map (fun c=>c.1 • (fderiv ℝ (P c.2) (B c.2 x)).comp (B c.2))).sum) x := by
    convert! hh using 1
  rw [hh'.fderiv]
  unfold chargedDirectionalScore
  rw [ContinuousLinearMap.sub_apply,clm_list_apply]
  simp only [List.map_map,Function.comp_def,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,smul_eq_mul]

theorem contDiff_chargedLogPotential (L : E→L[ℝ]ℝ) (cs : List (ℝ×A))
    (P : A→H→ℝ) (B : A→E→L[ℝ]H) (hP : ∀a,ContDiff ℝ 2 (P a)) :
    ContDiff ℝ 2 (chargedLogPotential L cs P B) := by
  have hc : ContDiff ℝ 2 (fun x=>(cs.map (fun c=>c.1*P c.2 (B c.2 x))).sum) := by
    induction cs with
    | nil => exact contDiff_const
    | cons c cs ih =>
      convert (contDiff_const (c:=c.1)).mul ((hP c.2).comp (B c.2).contDiff) |>.add ih using 1
      funext x
      simp only [List.map_cons,List.sum_cons,Function.comp_apply]
  exact L.contDiff.sub hc

theorem exponentialDensityHessian_chargedLogPotential (L : E→L[ℝ]ℝ) (cs : List (ℝ×A))
    (P : A→H→ℝ) (B : A→E→L[ℝ]H) (hP : ∀a,ContDiff ℝ 2 (P a)) (x v : E) :
    exponentialDensityHessian (chargedLogPotential L cs P B) x v v=
      -chargedDirectionalCurvature cs P B x v := by
  have hd:=hasFDerivAt_weighted_list cs
    (fun a y=>fderiv ℝ (P a) (B a y) (B a v))
    (fun a=>((exponentialDensityHessian (P a) (B a x)).flip (B a v)).comp (B a)) x
    (fun a=>(hasFDerivAt_exponential_directional_field (P a) (hP a) (B a x) (B a v)).comp x
      (B a).hasFDerivAt)
  have hh:=(hasFDerivAt_const (L v) x).sub hd
  have he : (fun y=>fderiv ℝ (chargedLogPotential L cs P B) y v)=
      (fun y=>L v-(cs.map (fun c=>c.1*fderiv ℝ (P c.2) (B c.2 y) (B c.2 v))).sum) :=
    funext fun y=>fderiv_chargedLogPotential L cs P B hP y v
  have hl:=hasFDerivAt_exponential_directional_field (chargedLogPotential L cs P B)
    (contDiff_chargedLogPotential L cs P B hP) x v
  rw [he] at hl
  have hv:=congrArg (fun D : E→L[ℝ]ℝ=>D v) (hl.unique hh)
  simp only [ContinuousLinearMap.flip_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply,zero_sub,ContinuousLinearMap.neg_apply] at hv
  rw [clm_list_apply] at hv
  simpa only [chargedDirectionalCurvature,List.map_map,Function.comp_def,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,smul_eq_mul] using hv

theorem exponentialDensityHessian_exp_chargedLogPotential (L : E→L[ℝ]ℝ) (cs : List (ℝ×A))
    (P : A→H→ℝ) (B : A→E→L[ℝ]H) (hP : ∀a,ContDiff ℝ 2 (P a)) (x v : E) :
    exponentialDensityHessian (fun y=>Real.exp (chargedLogPotential L cs P B y)) x v v=
      Real.exp (chargedLogPotential L cs P B x)*
        ((chargedDirectionalScore L cs P B x v)^2-chargedDirectionalCurvature cs P B x v) := by
  rw [exponentialDensityHessian_exp_potential _ (contDiff_chargedLogPotential L cs P B hP),
    exponentialDensityHessian_chargedLogPotential L cs P B hP,
    fderiv_chargedLogPotential L cs P B hP]
  ring

end FourPapersCommon
