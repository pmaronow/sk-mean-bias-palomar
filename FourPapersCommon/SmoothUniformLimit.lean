module
public import FourPapersCommon.UniformDerivativeLimit
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section

/-! A genuine smooth uniform limit from uniform bounds on all positive jets.
Every derivative is identified through the derivative limit theorem. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem norm_secondJet_iteratedFDeriv (f : E→F) (hf : ContDiff ℝ ∞ f) (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ r f) x‖=
      ‖iteratedFDeriv ℝ (r+2) f x‖ := by
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r+1) => E) F
  rw [←norm_iteratedFDeriv_fderiv,fderiv_iteratedFDeriv]
  change ‖iteratedFDeriv ℝ 1 (L ∘ iteratedFDeriv ℝ (r+1) f) x‖=_
  rw [L.norm_iteratedFDeriv_comp_left (iteratedFDeriv ℝ (r+1) f) x 1]
  rw [norm_iteratedFDeriv_one,norm_fderiv_iteratedFDeriv]

theorem lipschitz_fderiv_of_secondJet_bound (f : E→F) (hf : ContDiff ℝ ∞ f)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀x,‖iteratedFDeriv ℝ 2 f x‖ ≤ C) :
    LipschitzWith C.toNNReal (fderiv ℝ f) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp))
  intro x
  rw [←NNReal.coe_le_coe,coe_nnnorm,Real.coe_toNNReal _ hC,
    ←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
  exact hB x

theorem contDiff_uniformLimit_of_uniform_jet_bounds (f : ℕ→E→F) (g : E→F)
    (hf : ∀j,ContDiff ℝ ∞ (f j)) (C : ℕ→ℝ) (hC : ∀r,0 ≤ C r)
    (hB : ∀r,2 ≤ r → ∀j x,‖iteratedFDeriv ℝ r (f j) x‖ ≤ C r)
    (hu : TendstoUniformly f g atTop) :
    ContDiff ℝ ∞ g ∧ ∀r,TendstoUniformly (fun j => iteratedFDeriv ℝ r (f j))
      (iteratedFDeriv ℝ r g) atTop := by
  have advance (r : ℕ) (hr : TendstoUniformly (fun j => iteratedFDeriv ℝ r (f j))
      (iteratedFDeriv ℝ r g) atTop) :
      Differentiable ℝ (iteratedFDeriv ℝ r g) ∧
      TendstoUniformly (fun j => iteratedFDeriv ℝ (r+1) (f j)) (iteratedFDeriv ℝ (r+1) g) atTop := by
    have hs (j : ℕ) : ContDiff ℝ ∞ (iteratedFDeriv ℝ r (f j)) :=
      (hf j).iteratedFDeriv_right (by simp)
    have hL (j : ℕ) : LipschitzWith (C (r+2)).toNNReal
        (fderiv ℝ (iteratedFDeriv ℝ r (f j))) :=
      lipschitz_fderiv_of_secondJet_bound _ (hs j) _ (hC _) (fun x => by
        rw [norm_secondJet_iteratedFDeriv (f j) (hf j)]
        exact hB (r+2) (by omega) j x)
    obtain ⟨D,hD,hd,hDc⟩ := exists_uniform_derivative_limit
      (fun j => iteratedFDeriv ℝ r (f j)) (iteratedFDeriv ℝ r g)
      (fun j => (hs j).of_le (by simp)) (C (r+2)).toNNReal hL hr
    have he : D=fderiv ℝ (iteratedFDeriv ℝ r g) := funext fun x => (hd x).fderiv.symm
    rw [he] at hD
    refine ⟨fun x => (hd x).differentiableAt,?_⟩
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r+1) => E) F).symm
    have hh := L.isometry.uniformContinuous.comp_tendstoUniformly hD
    simpa only [iteratedFDeriv_succ_eq_comp_left,Function.comp_def] using hh
  have hU (r : ℕ) : TendstoUniformly (fun j => iteratedFDeriv ℝ r (f j))
      (iteratedFDeriv ℝ r g) atTop := by
    induction r with
    | zero =>
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def] using
        (continuousMultilinearCurryFin0 ℝ E F).symm.isometry.uniformContinuous.comp_tendstoUniformly hu
    | succ r ih => exact (advance r ih).2
  refine ⟨contDiff_of_differentiable_iteratedFDeriv (fun r _ => (advance r (hU r)).1),hU⟩

end FourPapersCommon
