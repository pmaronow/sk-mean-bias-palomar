module
public import FourPapersCommon.SmoothUniformLimit

@[expose] public section

/-! A genuine C² uniform limit from uniform second and third derivatives.
The first and second derivatives are constructed and identified by uniform
derivative limits. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiff_two_uniformLimit_of_uniform_jet_bounds (f : ℕ → E → F) (g : E → F)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (C2 C3 : ℝ) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (h2 : ∀ j x, ‖iteratedFDeriv ℝ 2 (f j) x‖ ≤ C2)
    (h3 : ∀ j x, ‖iteratedFDeriv ℝ 3 (f j) x‖ ≤ C3)
    (hu : TendstoUniformly f g atTop) :
    ContDiff ℝ 2 g ∧
      TendstoUniformly (fun j => fderiv ℝ (f j)) (fderiv ℝ g) atTop ∧
      TendstoUniformly (fun j => fderiv ℝ (fderiv ℝ (f j)))
        (fderiv ℝ (fderiv ℝ g)) atTop := by
  have hL j := lipschitz_fderiv_of_secondJet_bound (f j) (hf j) C2 hC2 (h2 j)
  obtain ⟨D,hD,hd,hDc⟩ := exists_uniform_derivative_limit f g
    (fun j => (hf j).of_le (by simp)) C2.toNNReal hL hu
  have he : D=fderiv ℝ g := funext fun x => (hd x).fderiv.symm
  rw [he] at hD hd hDc
  have hs j : ContDiff ℝ ∞ (fderiv ℝ (f j)) := (hf j).fderiv_right (by simp)
  have hL1 j : LipschitzWith C3.toNNReal (fderiv ℝ (fderiv ℝ (f j))) :=
    lipschitz_fderiv_of_secondJet_bound _ (hs j) C3 hC3 (fun x => by
      rw [norm_iteratedFDeriv_fderiv]
      exact h3 j x)
  obtain ⟨D2,hD2,hd2,hD2c⟩ := exists_uniform_derivative_limit
    (fun j => fderiv ℝ (f j)) (fderiv ℝ g)
    (fun j => (hs j).of_le (by simp)) C3.toNNReal hL1 hD
  have he2 : D2=fderiv ℝ (fderiv ℝ g) := funext fun x => (hd2 x).fderiv.symm
  rw [he2] at hD2 hd2 hD2c
  refine ⟨?_,hD,hD2⟩
  have h1 : ContDiff ℝ 1 (fderiv ℝ g) :=
    contDiff_one_iff_hasFDerivAt.mpr ⟨_,hD2c,hd2⟩
  have htwo : ContDiff ℝ (1+1) g := contDiff_succ_iff_fderiv.mpr
    ⟨fun x => (hd x).differentiableAt,by simp,h1⟩
  simpa only [one_add_one_eq_two] using htwo

end FourPapersCommon
