module
public import FourPapersCommon.RetainedJetLinearChange
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

/-! Uniform exponential retained-jet bounds with an outside parameter on
a closed set. Only the retained variables are differentiated. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 128
variable {A E F G : Type*} [TopologicalSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure RetainedJetExponentialOn (f : A→E→F) (Q : Set A) (V : Set E) : Prop
    extends RetainedJetContinuousOn f Q V where
  bound : ∀r : ℕ,∃C R : ℝ,0≤C∧0≤R∧∀q∈Q,∀x∈V,
    ‖iteratedFDeriv ℝ r (f q) x‖≤C*Real.exp (R*‖x‖)

theorem RetainedJetExponentialOn.congr {f g : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedJetExponentialOn f Q V)
    (he : ∀q∈Q,∀x∈V,f q=ᶠ[𝓝 x]g q) : RetainedJetExponentialOn g Q V := by
  refine ⟨hf.toRetainedJetContinuousOn.congr he,?_⟩
  intro r
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound r
  refine ⟨C,R,hC,hR,fun q hq x hx=>?_⟩
  rw [←((he q hq x hx).iteratedFDeriv ℝ r).eq_of_nhds]
  exact hb q hq x hx

theorem RetainedJetExponentialOn.compCLM {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedJetExponentialOn f Q V) (L : F→L[ℝ]G) :
    RetainedJetExponentialOn (fun q x=>L (f q x)) Q V := by
  refine ⟨hf.toRetainedJetContinuousOn.compCLM L,?_⟩
  intro r
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound r
  refine ⟨‖L‖*C,R,mul_nonneg (norm_nonneg _) hC,hR,fun q hq x hx=>?_⟩
  exact (L.norm_iteratedFDeriv_comp_left (hf.smooth q hq x hx) (by simp)).trans
    ((mul_le_mul_of_nonneg_left (hb q hq x hx) (norm_nonneg _)).trans_eq (by ring))

theorem RetainedJetExponentialOn.fderiv {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedJetExponentialOn f Q V) :
    RetainedJetExponentialOn (fun q=>_root_.fderiv ℝ (f q)) Q V := by
  refine ⟨hf.toRetainedJetContinuousOn.fderiv,?_⟩
  intro r
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound (r+1)
  exact ⟨C,R,hC,hR,fun q hq x hx=>by simpa only [norm_iteratedFDeriv_fderiv] using hb q hq x hx⟩

theorem RetainedJetExponentialOn.directional {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedJetExponentialOn f Q V) (v : E) :
    RetainedJetExponentialOn (fun q x=>_root_.fderiv ℝ (f q) x v) Q V :=
  hf.fderiv.compCLM (ContinuousLinearMap.apply ℝ F v)

theorem RetainedJetExponentialOn.precompIsometry {f : A→E→F} {Q : Set A} {V : Set E}
    (hf : RetainedJetExponentialOn f Q V) (L : G≃ₗᵢ[ℝ]E) (W : Set G)
    (hL : ∀x∈W,L x∈V) : RetainedJetExponentialOn (fun q x=>f q (L x)) Q W := by
  refine ⟨hf.toRetainedJetContinuousOn.precompCLM L.toContinuousLinearEquiv.toContinuousLinearMap W hL,?_⟩
  intro r
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound r
  refine ⟨C,R,hC,hR,fun q hq x hx=>?_⟩
  change ‖iteratedFDeriv ℝ r ((f q) ∘ L) x‖≤C*Real.exp (R*‖x‖)
  rw [L.norm_iteratedFDeriv_comp_right,←L.norm_map x]
  exact hb q hq (L x) (hL x hx)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem RetainedJetExponentialOn.partialFDeriv {f : A→P×E→F} {Q : Set A} {V : Set (P×E)}
    (hf : RetainedJetExponentialOn f Q V) (hV : IsOpen V) :
    RetainedJetExponentialOn (fun q z=>_root_.fderiv ℝ (fun x=>f q (z.1,x)) z.2) Q V := by
  let L : ((P×E)→L[ℝ]F)→L[ℝ](E→L[ℝ]F):=
    (ContinuousLinearMap.compL ℝ E (P×E) F).flip (ContinuousLinearMap.inr ℝ P E)
  apply (hf.fderiv.compCLM L).congr
  intro q hq z hz
  filter_upwards [hV.mem_nhds hz] with w hw
  exact (partial_fderiv_eq (f q) w.1 w.2 ((hf.smooth q hq w hw).differentiableAt (by simp))).symm

theorem RetainedJetExponentialOn.partialGradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : A→P×E→ℝ} {Q : Set A} {V : Set (P×E)}
    (hf : RetainedJetExponentialOn f Q V) (hV : IsOpen V) :
    RetainedJetExponentialOn (fun q z=>gradient (fun x=>f q (z.1,x)) z.2) Q V :=
  (hf.partialFDeriv hV).compCLM
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem RetainedJetExponentialOn.partialHessian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {f : A→P×E→ℝ} {Q : Set A} {V : Set (P×E)}
    (hf : RetainedJetExponentialOn f Q V) (hV : IsOpen V) :
    RetainedJetExponentialOn (fun q z=>QuantitativeFollowup.hessianOperator
      (fun x=>f q (z.1,x)) z.2) Q V := by
  apply ((hf.partialGradient hV).partialFDeriv hV).congr
  intro q hq z hz
  filter_upwards [hV.mem_nhds hz] with w hw
  have hC : ContDiffAt ℝ 2 (fun x=>f q (w.1,x)) w.2:=
    ((hf.smooth q hq w hw).comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num)
  exact (hasFDerivAt_gradient_of_contDiffAt _ w.2 hC).fderiv

end FourPapersCommon
