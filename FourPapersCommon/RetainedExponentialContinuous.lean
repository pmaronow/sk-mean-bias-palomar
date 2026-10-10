module
public import FourPapersCommon.RetainedJetBounds
public import DepthPaper.InverseDerivativeBounds

@[expose] public section

/-! Continuous exponential value bounds on closed outside-parameter sets.
These are sufficient for endpoint dominated convergence. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {A E F G H : Type*} [TopologicalSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

structure RetainedExponentialContinuousOn (f : A→E→F) (Q : Set A) (V : Set E) : Prop where
  continuous : ContinuousOn (fun w : A×E=>f w.1 w.2) (Q×ˢV)
  bound : ∃C R : ℝ,0≤C∧0≤R∧∀q∈Q,∀x∈V,‖f q x‖≤C*Real.exp (R*‖x‖)

theorem RetainedJetExponentialOn.values {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedJetExponentialOn f Q V) : RetainedExponentialContinuousOn f Q V := by
  refine ⟨hf.toRetainedJetContinuousOn.values,?_⟩
  simpa only [norm_iteratedFDeriv_zero] using hf.bound 0

theorem RetainedExponentialContinuousOn.congr {f g : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedExponentialContinuousOn f Q V)
    (he : ∀q∈Q,∀x∈V,f q x=g q x) : RetainedExponentialContinuousOn g Q V := by
  refine ⟨hf.continuous.congr (fun w hw=>(he w.1 hw.1 w.2 hw.2).symm),?_⟩
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound
  exact ⟨C,R,hC,hR,fun q hq x hx=>by rw [←he q hq x hx];exact hb q hq x hx⟩

theorem RetainedExponentialContinuousOn.compCLM {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedExponentialContinuousOn f Q V) (L : F→L[ℝ]G) :
    RetainedExponentialContinuousOn (fun q x=>L (f q x)) Q V := by
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound
  refine ⟨L.continuous.comp_continuousOn hf.continuous,
    ‖L‖*C,R,mul_nonneg (norm_nonneg _) hC,hR,fun q hq x hx=>?_⟩
  exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hb q hq x hx) (norm_nonneg _)).trans_eq (by ring))

theorem RetainedExponentialContinuousOn.bilinear {f : A→E→F} {g : A→E→G}
    {Q : Set A} {V : Set E} (hf : RetainedExponentialContinuousOn f Q V)
    (hg : RetainedExponentialContinuousOn g Q V) (B : F→L[ℝ]G→L[ℝ]H) :
    RetainedExponentialContinuousOn (fun q x=>B (f q x) (g q x)) Q V := by
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound
  obtain ⟨D,S,hD,hS,hd⟩:=hg.bound
  refine ⟨B.isBoundedBilinearMap.continuous.comp_continuousOn (hf.continuous.prodMk hg.continuous),
    ‖B‖*C*D,R+S,by positivity,add_nonneg hR hS,fun q hq x hx=>?_⟩
  apply ((B (f q x)).le_opNorm (g q x)).trans
  apply (mul_le_mul ((B.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hb q hq x hx) (norm_nonneg _))) (hd q hq x hx)
    (norm_nonneg _) (by positivity)).trans_eq
  simp only [add_mul,Real.exp_add]
  ring

theorem RetainedExponentialContinuousOn.neg {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedExponentialContinuousOn f Q V) :
    RetainedExponentialContinuousOn (fun q x=> -f q x) Q V := by
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound
  exact ⟨hf.continuous.neg,C,R,hC,hR,fun q hq x hx=>by simpa only [norm_neg] using hb q hq x hx⟩

theorem RetainedExponentialContinuousOn.add {f g : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedExponentialContinuousOn f Q V) (hg : RetainedExponentialContinuousOn g Q V) :
    RetainedExponentialContinuousOn (fun q x=>f q x+g q x) Q V := by
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound
  obtain ⟨D,S,hD,hS,hd⟩:=hg.bound
  refine ⟨hf.continuous.add hg.continuous,C+D,R+S,add_nonneg hC hD,add_nonneg hR hS,fun q hq x hx=>?_⟩
  apply (norm_add_le _ _).trans
  have hR' : Real.exp (R*‖x‖)≤Real.exp ((R+S)*‖x‖):=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS) (norm_nonneg _))
  have hS' : Real.exp (S*‖x‖)≤Real.exp ((R+S)*‖x‖):=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hR) (norm_nonneg _))
  exact (add_le_add ((hb q hq x hx).trans (mul_le_mul_of_nonneg_left hR' hC))
    ((hd q hq x hx).trans (mul_le_mul_of_nonneg_left hS' hD))).trans_eq (by ring)

end FourPapersCommon
