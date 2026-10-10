module
public import QuantitativePaper.GaussianColeHopfCoordinateJets

@[expose] public section

/-! Actual affine pullback of local joint jet bounds. This transports the
independent mass coordinate to an affine profile parameter. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1400000
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem iteratedFDeriv_affine_on_open (f : E → F) (V : Set E) (hV : IsOpen V)
    {N j : ℕ} (hf : ContDiffOn ℝ N f V) (hj : j≤N)
    (L : G →L[ℝ] E) (c : E) (x : G) (hx : L x+c∈V) :
    iteratedFDeriv ℝ j (fun y => f (L y+c)) x =
      (iteratedFDeriv ℝ j f (L x+c)).compContinuousLinearMap (fun _ => L) := by
  let H : E → F := fun y => f (y+c)
  let W := (fun y : E => y+c) ⁻¹' V
  have hW : IsOpen W := hV.preimage (continuous_id.add continuous_const)
  have hH : ContDiffOn ℝ N H W := hf.comp
    (contDiff_id.add contDiff_const).contDiffOn (fun _ h => h)
  change iteratedFDeriv ℝ j (H ∘ L) x = _
  rw [iteratedFDeriv_comp_linear_on_open H W hW hH hj L x hx,iteratedFDeriv_comp_add_right]

theorem affine_smooth_exp_jets_on_open (N : ℕ) (f : E → F)
    (V : Set E) (hV : IsOpen V) (hf : ContDiffOn ℝ N f V)
    (L : G →L[ℝ] E) (c : E) (U : Set G) (hU : IsOpen U)
    (hmap : ∀ x∈U,L x+c∈V) (K D : ℝ) (hK : 1≤K) (hD : 0≤D)
    (hjets : ∀ j,1≤j → j≤N → ∀ y∈V,
      ‖iteratedFDeriv ℝ j f y‖≤(K*Real.exp (D*‖y‖))^j) :
    ContDiffOn ℝ N (fun x => f (L x+c)) U ∧
      ∃ C Q : ℝ,1≤C ∧1≤Q ∧ ∀ j,1≤j → j≤N → ∀ x∈U,
        ‖iteratedFDeriv ℝ j (fun y => f (L y+c)) x‖≤(C*Real.exp (Q*‖x‖))^j := by
  let M := max 1 ‖L‖
  let C := max 1 (K*Real.exp (D*‖c‖)*M)
  let Q := max 1 (D*‖L‖)
  refine ⟨hf.comp (L.contDiff.add contDiff_const).contDiffOn hmap,
    C,Q,le_max_left _ _,le_max_left _ _,?_⟩
  intro j hj0 hj x hx
  rw [iteratedFDeriv_affine_on_open f V hV hf hj L c x (hmap x hx)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hp := mul_le_mul_of_nonneg_right (hjets j hj0 hj (L x+c) (hmap x hx))
    (pow_nonneg (norm_nonneg L) j)
  apply hp.trans
  rw [←mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hn : ‖L x+c‖≤‖L‖*‖x‖+‖c‖ :=
    (norm_add_le _ _).trans (add_le_add_left (L.le_opNorm x) _)
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hD)
  have hh := mul_le_mul_of_nonneg_left he (zero_le_one.trans hK)
  have hM : ‖L‖≤M := le_max_right _ _
  have he' : Real.exp ((D*‖L‖)*‖x‖)≤Real.exp (Q*‖x‖) := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  calc
    K*Real.exp (D*‖L x+c‖)*‖L‖ ≤ K*Real.exp (D*(‖L‖*‖x‖+‖c‖))*M :=
      mul_le_mul hh hM (norm_nonneg _) (by positivity)
    _ = (K*Real.exp (D*‖c‖)*M)*Real.exp ((D*‖L‖)*‖x‖) := by
      rw [mul_add,Real.exp_add]
      ring
    _ ≤ C*Real.exp (Q*‖x‖) := mul_le_mul (le_max_right _ _) he' (Real.exp_pos _).le
      (by dsimp [C];positivity)

end QuantitativePaper
