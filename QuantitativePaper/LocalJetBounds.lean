module
public import QuantitativePaper.LogJetBounds
public import QuantitativePaper.LocalSmoothIntegralJets

@[expose] public section

/-! Ordinary jet bounds on open parameter domains. These local versions use
the actual function and avoid extending positive masses through zero. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_comp_le_on_open {N j : ℕ} (f : E → ℝ) (g : ℝ → ℝ)
    (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) (hg : ContDiff ℝ N g)
    (hj : j ≤ N) (x : E) (hx : x ∈ U) (C D : ℝ)
    (hC : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ (j.factorial:ℝ)*C*D^j := by
  have hh := norm_iteratedFDerivWithin_comp_le (n := j) hg.contDiffOn hf (by exact_mod_cast hj)
    uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ f U) hx
    (fun i hi => by simpa only [iteratedFDerivWithin_univ] using hC i hi)
    (fun i hi hij => by simpa only [iteratedFDerivWithin_of_isOpen i hU hx] using hD i hi hij)
  simpa only [iteratedFDerivWithin_of_isOpen j hU hx] using hh

theorem norm_iteratedFDeriv_exp_le_on_open {N j : ℕ} (f : E → ℝ)
    (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    (hj : j ≤ N) (D : ℝ) (x : E) (hx : x ∈ U)
    (hD : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ j (fun y => Real.exp (f y)) x‖ ≤
      (j.factorial:ℝ)*Real.exp (f x)*D^j := by
  apply norm_iteratedFDeriv_comp_le_on_open f Real.exp U hU hf Real.contDiff_exp hj x hx
    (Real.exp (f x)) D ?_ hD
  intro i _
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  exact le_of_eq (Real.norm_of_nonneg (Real.exp_pos _).le)

theorem norm_iteratedFDeriv_mul_le_on_open {N j : ℕ} (f g : E → ℝ)
    (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) (hg : ContDiffOn ℝ N g U)
    (hj : j ≤ N) (x : E) (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖ ≤
      ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (j-i) g x‖ := by
  have hh := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx (by norm_cast : (j:ℕ∞ω) ≤ N)
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hx] using hh

theorem norm_iteratedFDeriv_log_le_of_relative_on_open {N j : ℕ} (f : E → ℝ)
    (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    (hpos : ∀ y ∈ U, 0 < f y) (hj0 : 1 ≤ j) (hj : j ≤ N)
    (K : ℝ) (x : E) (hxU : x ∈ U)
    (hrelative : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ K^i*f x) :
    ‖iteratedFDeriv ℝ j (fun y => Real.log (f y)) x‖ ≤
      (j.factorial:ℝ)*logJetCoefficient j*K^j := by
  let h := fun y => (f x)⁻¹*f y
  have hh : ContDiffOn ℝ N h U := contDiffOn_const.mul hf
  have hx : h x = 1 := inv_mul_cancel₀ (hpos x hxU).ne'
  have hr : MapsTo h U ({0}ᶜ:Set ℝ) := by
    intro y hy
    exact (mul_pos (inv_pos.mpr (hpos x hxU)) (hpos y hy)).ne'
  have hC (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i Real.log ({0}ᶜ:Set ℝ) (h x)‖ ≤ logJetCoefficient j := by
    rw [hx]
    unfold logJetCoefficient
    exact Finset.single_le_sum
      (f := fun i => ‖iteratedFDerivWithin ℝ i Real.log ({0}ᶜ:Set ℝ) 1‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  have hD (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDerivWithin ℝ i h U x‖ ≤ K^i := by
    rw [iteratedFDerivWithin_of_isOpen i hU hxU]
    have hfi : ContDiffAt ℝ i f x :=
      (hf.of_le (by norm_cast; omega)).contDiffAt (hU.mem_nhds hxU)
    have he : iteratedFDeriv ℝ i h x = (f x)⁻¹ • iteratedFDeriv ℝ i f x := by
      simpa only [h, smul_eq_mul] using iteratedFDeriv_const_smul_apply' (a := (f x)⁻¹) hfi
    rw [he, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hpos x hxU)]
    apply (inv_mul_le_iff₀ (hpos x hxU)).mpr
    simpa only [mul_comm] using hrelative i hi hij
  have hb := norm_iteratedFDerivWithin_comp_le (n := j) Real.contDiffOn_log hh (by exact_mod_cast hj)
    isOpen_compl_singleton.uniqueDiffOn hU.uniqueDiffOn hr hxU hC hD
  rw [iteratedFDerivWithin_of_isOpen j hU hxU] at hb
  have he : (fun y => Real.log (f y)) =ᶠ[𝓝 x]
      fun y => Real.log (h y)+Real.log (f x) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    unfold h
    rw [Real.log_mul (inv_ne_zero (hpos x hxU).ne') (hpos y hy).ne', Real.log_inv]
    ring
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  change ‖iteratedFDeriv ℝ j ((Real.log ∘ h)+(fun _ => Real.log (f x))) x‖ ≤ _
  rw [iteratedFDeriv_add_apply]
  · rw [iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, add_zero]
    exact hb
  · exact (((hh.of_le (by norm_cast)).contDiffAt (hU.mem_nhds hxU)).log (hr hxU)).of_le le_rfl
  · exact contDiffAt_const

end QuantitativePaper
