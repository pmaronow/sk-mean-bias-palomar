module
public import QuantitativeFollowup.FollowupCavityContractionAbsorption

@[expose] public section

/-! Scalar closure of the genuine trace, signed-response, third-moment
and coefficient-one comparison estimates. The physical trace identity
and its actual Taylor remainder are separate inputs to this reducer. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000

def followupCavityClosureScale (β CR : ℝ) : ℝ :=
  1 + 192*β^2*Real.exp (43*β^2) + 64*CR*Real.exp (21*β^2) +
    46080*β^2*(Real.exp (21*β^2))^2

def followupCavityClosureConstant (β CR : ℝ) : ℝ :=
  4*followupCavityClosureScale β CR+2

theorem followupCavityClosureConstant_one_le (β CR : ℝ) (hCR : 0 ≤ CR) :
    1 ≤ followupCavityClosureConstant β CR := by
  have h : 0 ≤ followupCavityClosureScale β CR := by
    unfold followupCavityClosureScale
    positivity
  unfold followupCavityClosureConstant
  linarith

theorem cavityFullTrace_scalar_closure (n : ℕ) (hn : 0 < n)
    (β ρ CR V Vminus Vsite tracePart penalty signed R M3 A J H : ℝ)
    (hρ : ρ ∈ Ioc (0 : ℝ) 1) (hCR : 0 ≤ CR)
    (hV : 0 ≤ V) (hVm : 0 ≤ Vminus) (hSite : Vsite ≤ 1/4)
    (hPenalty : 0 ≤ penalty) (hA : 0 ≤ A) (hJ : 0 ≤ J) (hH : 0 ≤ H)
    (hTrace : V = Vsite/((n+1 : ℕ) : ℝ) + (n : ℝ)/((n+1 : ℕ) : ℝ)*
      (tracePart-penalty+signed+R))
    (hOrder : tracePart ≤ (1-3*ρ/4)*Vminus)
    (hSigned : |signed| ≤ 192*β^2*Real.exp (43*β^2)*
      (A+J+1/((n+1 : ℕ) : ℝ)^2))
    (hRem : |R| ≤ CR*M3)
    (hThermal : M3 ≤ Real.exp (21*β^2)*
      (64*(A+J)+16*H+32/((n+1 : ℕ) : ℝ)^3))
    (hComparison : Vminus ≤ V+720*β^2*Real.exp (21*β^2)*M3+1/(4*(n : ℝ)^2)) :
    (3*ρ/4)*V ≤ followupCavityClosureConstant β CR*
      (1/((n+1 : ℕ) : ℝ)+A+J+H) := by
  let N : ℝ := ((n+1 : ℕ) : ℝ)
  let B : ℝ := 1/N+A+J+H
  let E : ℝ := Real.exp (21*β^2)
  let S : ℝ := 192*β^2*Real.exp (43*β^2)
  let C : ℝ := followupCavityClosureScale β CR
  let θ : ℝ := 1-3*ρ/4
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hN : N = (n : ℝ)+1 := by simp [N]
  have hNp : 0 < N := by dsimp only [N]; positivity
  have hN1 : 1 ≤ N := by linarith
  have hInv : 0 ≤ 1/N := by positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hC : 0 ≤ C := by dsimp only [C, followupCavityClosureScale]; positivity
  have hSterm : 0 ≤ 192*β^2*Real.exp (43*β^2) := by positivity
  have hRterm : 0 ≤ 64*CR*Real.exp (21*β^2) := by positivity
  have hMterm : 0 ≤ 46080*β^2*(Real.exp (21*β^2))^2 := by positivity
  have hSC : S ≤ C := by
    dsimp only [S, C, followupCavityClosureScale]
    linarith
  have hRC : 64*CR*E ≤ C := by
    dsimp only [E, C, followupCavityClosureScale]
    linarith
  have hMC : 46080*β^2*E^2 ≤ C := by
    dsimp only [E, C, followupCavityClosureScale]
    linarith
  have hInv2 : 1/N^2 ≤ 1/N := by
    apply (div_le_div_iff₀ (by positivity : 0 < N^2) hNp).mpr
    nlinarith
  have hInv3 : 1/N^3 ≤ 1/N := by
    apply (div_le_div_iff₀ (by positivity : 0 < N^3) hNp).mpr
    have hh := mul_le_mul_of_nonneg_left (by nlinarith : 1 ≤ N^2) hNp.le
    nlinarith only [hh]
  have hDelta : 1/(4*(n : ℝ)^2) ≤ 1/N := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*(n : ℝ)^2) hNp).mpr
    nlinarith
  have hM : M3 ≤ 64*E*B := by
    have hb : 64*(A+J)+16*H+32/N^3 ≤ 64*B := by
      dsimp only [B]
      simp only [div_eq_mul_inv] at hInv3 hInv ⊢
      nlinarith only [hInv3, hInv, hH]
    exact hThermal.trans ((mul_le_mul_of_nonneg_left hb hE).trans_eq (by ring))
  have hs : signed ≤ C*B := by
    have hb : A+J+1/N^2 ≤ B := by dsimp only [B]; linarith
    exact (le_abs_self signed).trans (hSigned.trans
      ((mul_le_mul_of_nonneg_left hb hS).trans (mul_le_mul_of_nonneg_right hSC hB)))
  have hr : R ≤ C*B := by
    calc
      R ≤ |R| := le_abs_self R
      _ ≤ CR*M3 := hRem
      _ ≤ CR*(64*E*B) := mul_le_mul_of_nonneg_left hM hCR
      _ = (64*CR*E)*B := by ring
      _ ≤ C*B := mul_le_mul_of_nonneg_right hRC hB
  have hrest : Vminus ≤ V+C*B+1/(4*(n : ℝ)^2) := by
    have hc : 0 ≤ 720*β^2*E := by positivity
    have hm := mul_le_mul_of_nonneg_left hM hc
    have hc' := mul_le_mul_of_nonneg_right hMC hB
    nlinarith only [hComparison, hm, hc']
  have hθ : 0 ≤ θ := by dsimp only [θ]; linarith [hρ.2]
  have hθ1 : θ ≤ 1 := by dsimp only [θ]; linarith [hρ.1]
  have hRatio : (n : ℝ)/N ∈ Icc (0 : ℝ) 1 := by
    exact ⟨div_nonneg (by positivity) hNp.le, (div_le_one hNp).mpr (by linarith)⟩
  have hUpper : 0 ≤ θ*Vminus+2*C*B := by positivity
  have hbracket : tracePart-penalty+signed+R ≤ θ*Vminus+2*C*B := by
    change tracePart ≤ θ*Vminus at hOrder
    linarith
  have hfull : V ≤ (1/4)/N+θ*Vminus+2*C*B := by
    calc
      V = Vsite/N+(n : ℝ)/N*(tracePart-penalty+signed+R) := hTrace
      _ ≤ (1/4)/N+(n : ℝ)/N*(θ*Vminus+2*C*B) :=
        add_le_add (div_le_div_of_nonneg_right hSite hNp.le)
          (mul_le_mul_of_nonneg_left hbracket hRatio.1)
      _ ≤ (1/4)/N+(θ*Vminus+2*C*B) :=
        add_le_add le_rfl (mul_le_of_le_one_left hUpper hRatio.2)
      _ = _ := by ring
  have habs := cavityContraction_three_quarters_absorption V Vminus θ (2*C) B
    (1/(4*(n : ℝ)^2)) ((1/4)/N) ρ hV hρ.1.le hθ le_rfl
    (by positivity) hB (by positivity)
    (by nlinarith only [hrest, mul_nonneg hC hB]) hfull
  have hNsmall : (1/4)/N ≤ 1/N := div_le_div_of_nonneg_right (by norm_num) hNp.le
  have hbInv : 1/N ≤ B := by dsimp only [B]; linarith
  have hfinal : (3*ρ/4)*V ≤ (4*C+2)*B := by
    nlinarith only [habs, hDelta, hNsmall, hbInv]
  -- Both error terms were bounded by C*B; the shared reducer uses 2*C.
  -- Use the correspondingly enlarged source constant.
  simpa only [followupCavityClosureConstant] using hfinal

end QuantitativeFollowup
