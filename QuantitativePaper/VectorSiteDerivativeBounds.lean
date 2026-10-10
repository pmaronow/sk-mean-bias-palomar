module
public import QuantitativePaper.VectorIncidentEnergy

@[expose] public section

/-! Sharp actual incident-site magnetization derivative domination in
physical energy units, obtained from genuine finite-spin offset response. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2000000

theorem sitePrefixGaussianState_add_smul {n k N : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (j : Fin (N+1)) (g w : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) (r : ℝ) :
    sitePrefixGaussianState s β t i b j (g+r • w) =
      sitePrefixGaussianState s β t i b j g+r • sitePrefixGaussianState s β t i 0 j w := by
  have he : (g+r • w,b) = (g,b)+r • (w,0) := by
    apply Prod.ext <;> simp
  unfold sitePrefixGaussianState
  rw [he,map_add,map_smul,map_add,map_smul]
  rfl

theorem norm_fderiv_sitePrefixGaussianMagnetization_le {n k N : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : 0 < β) (ht : t ∈ Icc 0 1) (hN : N ≤ k+2) (i : Fin n)
    (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    ‖fderiv ℝ (sitePrefixGaussianMagnetization s β t i b) g‖ ≤
      sitePrefixGaussianCurvature s β t i b g := by
  let p := sitePrefixGaussianState s β t i b (Fin.last N) g
  let H := (vectorFieldHessian s β t p.1 (k+2-N) p.2 (EuclideanSpace.single i 1)) i
  have hH : 0 ≤ H := vectorFieldHessian_diagonal_nonneg s β t p.1 (k+2-N) p.2 i
  change ‖fderiv ℝ (sitePrefixGaussianMagnetization s β t i b) g‖ ≤ β*H
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hβ.le hH)
  intro w
  by_cases hw : w=0
  · subst w
    simp
  have hK : 0 < β*‖w‖ := mul_pos hβ (norm_pos_iff.mpr hw)
  let W := sitePrefixGaussianState s β t i 0 (Fin.last N) w
  let d : Configuration n → ℝ := fun σ => vectorTerminalExponent n β t W.1 W.2 σ/(β*‖w‖)
  have hd : ∀σ, |d σ|≤1 := by
    intro σ
    rw [abs_div,abs_of_pos hK]
    exact (div_le_one hK).mpr (siteTerminalEnergy_bound s β t hβ.le ht hN i σ w)
  have hb : vectorTerminalExponent n β t W.1 W.2 = fun σ => (β*‖w‖)*d σ := by
    funext σ
    dsimp [d]
    field_simp
  have hcross : |vectorObservableCrossResponse s β t p.1
      (vectorTerminalExponent n β t W.1 W.2) (fun σ => Paper.spinSign (σ i))
        (k+2-N) 0 p.2| ≤ β*‖w‖*H := by
    rw [hb,vectorObservableCrossResponse_const_mul_left_zero,abs_mul,abs_of_pos hK]
    exact mul_le_mul_of_nonneg_left
      (spin_offset_derivative_le_fieldHessian s β t p.1 d hd (k+2-N) p.2 i) hK.le
  have hdline : HasDerivAt (fun r : ℝ =>
      sitePrefixGaussianMagnetization s β t i b (g+r • w))
      (vectorObservableCrossResponse s β t p.1
        (vectorTerminalExponent n β t W.1 W.2) (fun σ => Paper.spinSign (σ i))
          (k+2-N) 0 p.2) 0 := by
    convert hasDerivAt_vectorMagnetization_joint_line s β t p.1 W.1 p.2 W.2 (k+2-N) i using 1
    funext r
    simp only [sitePrefixGaussianMagnetization,sitePrefixGaussianState_add_smul]
    rfl
  have hf := (contDiff_sitePrefixGaussianMagnetization s β t i b).differentiable
    (by norm_num) g
  have hh := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (((hasDerivAt_id (0:ℝ)).smul_const w).const_add g) (by simp)
  have heq := hh.unique hdline
  simp only [one_smul] at heq
  change ‖fderiv ℝ (sitePrefixGaussianMagnetization s β t i b) g w‖ ≤ _
  rw [heq,Real.norm_eq_abs]
  change _ ≤ (β*H)*‖w‖
  nlinarith [hcross]

end QuantitativePaper
