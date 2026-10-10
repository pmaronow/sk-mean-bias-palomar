module
public import DepthPaper.PointwiseDerivativeBounds
public import DepthPaper.InverseDerivativeBounds
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! Closure rules for actual smooth functions whose jets have exponential
growth. The sets may be unbounded; no compactness shortcut is used. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

structure ExponentialSmoothOn (f : E→F) (s : Set E) : Prop where
  smooth : ∀x∈s,ContDiffAt ℝ ∞ f x
  bound : ∀r : ℕ,∃C R : ℝ,0≤C ∧ 0≤R ∧ ∀x∈s,
    ‖iteratedFDeriv ℝ r f x‖≤C*Real.exp (R*‖x‖)

theorem ExponentialSmoothOn.common_bound {f : E→F} {s : Set E}
    (hf : ExponentialSmoothOn f s) (N : ℕ) :
    ∃C R : ℝ,1≤C ∧ 0≤R ∧ ∀r,r≤N→∀x∈s,
      ‖iteratedFDeriv ℝ r f x‖≤C*Real.exp (R*‖x‖) := by
  classical
  choose C R hC hR hb using fun i : Fin (N+1)=>hf.bound i.1
  let D:=1+∑i,C i
  let S:=∑i,R i
  have hsum : 0≤∑i,C i:=Finset.sum_nonneg fun i _=>hC i
  refine ⟨D,S,by dsimp [D];linarith,Finset.sum_nonneg (fun i _=>hR i),?_⟩
  intro r hr x hx
  let i : Fin (N+1):=⟨r,by omega⟩
  have hd : C i≤D:=by
    have hi:=Finset.single_le_sum (fun j _=>hC j) (Finset.mem_univ i)
    dsimp [D]
    linarith
  have hs : R i≤S:=Finset.single_le_sum (fun j _=>hR j) (Finset.mem_univ i)
  exact (hb i x hx).trans (mul_le_mul hd
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs (norm_nonneg _)))
    (Real.exp_pos _).le (by dsimp [D];linarith))

theorem ExponentialSmoothOn.congr {f g : E→F} {s : Set E}
    (hf : ExponentialSmoothOn f s) (he : ∀x∈s,f=ᶠ[𝓝 x]g) :
    ExponentialSmoothOn g s := by
  refine ⟨fun x hx=>(hf.smooth x hx).congr_of_eventuallyEq (he x hx).symm,fun r=>?_⟩
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound r
  exact ⟨C,R,hC,hR,fun x hx=>by
    rw [←((he x hx).iteratedFDeriv ℝ r).eq_of_nhds]
    exact hb x hx⟩

theorem ExponentialSmoothOn.compCLM {f : E→F} {s : Set E}
    (hf : ExponentialSmoothOn f s) (L : F→L[ℝ]G) :
    ExponentialSmoothOn (L∘f) s := by
  refine ⟨fun x hx=>L.contDiff.contDiffAt.comp x (hf.smooth x hx),fun r=>?_⟩
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound r
  refine ⟨‖L‖*C,R,mul_nonneg (norm_nonneg _) hC,hR,fun x hx=>?_⟩
  exact (L.norm_iteratedFDeriv_comp_left (hf.smooth x hx) (by simp)).trans
    ((mul_le_mul_of_nonneg_left (hb x hx) (norm_nonneg _)).trans_eq (by ring))

theorem ExponentialSmoothOn.fderiv {f : E→F} {s : Set E}
    (hf : ExponentialSmoothOn f s) : ExponentialSmoothOn (fderiv ℝ f) s := by
  refine ⟨fun x hx=>(hf.smooth x hx).fderiv_right (m:=∞) (by simp),fun r=>?_⟩
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound (r+1)
  exact ⟨C,R,hC,hR,fun x hx=>by
    simpa only [norm_iteratedFDeriv_fderiv] using hb x hx⟩

theorem ExponentialSmoothOn.bilinear {f : E→F} {g : E→G} {s : Set E}
    (hf : ExponentialSmoothOn f s) (hg : ExponentialSmoothOn g s)
    (B : F→L[ℝ]G→L[ℝ]H) :
    ExponentialSmoothOn (fun x=>B (f x) (g x)) s := by
  classical
  refine ⟨fun x hx=>B.isBoundedBilinearMap.contDiff.contDiffAt.comp₂
    (hf.smooth x hx) (hg.smooth x hx),fun r=>?_⟩
  obtain ⟨C,R,hC,hR,hfB⟩:=hf.common_bound r
  obtain ⟨D,S,hD,hS,hgB⟩:=hg.common_bound r
  refine ⟨‖B‖*(2:ℝ)^r*C*D,R+S,by positivity,add_nonneg hR hS,fun x hx=>?_⟩
  apply (DepthPaper.norm_iteratedFDeriv_bilinear_le_at B (hf.smooth x hx) (hg.smooth x hx) r).trans
  calc
    _≤‖B‖*∑i∈Finset.range (r+1),(r.choose i:ℝ)*
        (C*Real.exp (R*‖x‖))*(D*Real.exp (S*‖x‖)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro i hi
      have hir : i≤r:=by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfB i hir x hx) (Nat.cast_nonneg _))
        (hgB (r-i) (Nat.sub_le _ _) x hx) (norm_nonneg _) (by positivity)
    _=_:=by
      rw [←Finset.sum_mul,←Finset.sum_mul]
      have he : (∑i∈Finset.range (r+1),(r.choose i:ℝ))=(2:ℝ)^r:=by
        exact_mod_cast Nat.sum_range_choose r
      rw [he]
      simp only [add_mul,Real.exp_add]
      ring

end FourPapersCommon
