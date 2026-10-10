module
public import QuantitativePaper.GaussianColeHopfCoordinateSlope
public import QuantitativePaper.CompactParameterIntegralOnOpen

@[expose] public section

/-! Finite-order joint smoothing of the genuine removable coordinate quotient.
The compact FTC representation gives actual jets and uniform exponential
bounds, including on the zero-coordinate hyperplane. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1600000
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem smoothCoordinateSlope_smooth_exp_jets_on_open (N : ℕ)
    (f : ℝ×E → ℝ) (U : Set (ℝ×E)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ (N+1) f U)
    (hcontract : ∀ x ∈ U, ∀ r ∈ Icc (0:ℝ) 1, coordinateContraction r x ∈ U)
    (hzero : ∀ x, (0,x) ∈ U → f (0,x)=0)
    (K D : ℝ) (hK : 1 ≤ K) (hD : 0 ≤ D)
    (hjets : ∀ j, 1 ≤ j → j ≤ N+1 → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j f x‖ ≤ (K*Real.exp (D*‖x‖))^j) :
    ContDiffOn ℝ N (smoothCoordinateSlope f) U ∧
      ∀ j, 1 ≤ j → j ≤ N → ∀ x ∈ U,
        ‖iteratedFDeriv ℝ j (smoothCoordinateSlope f) x‖ ≤
          (K^2*Real.exp ((2*D)*‖x‖))^j := by
  let H : (ℝ×E) → ℝ → ℝ := fun x r => coordinateDerivative f (coordinateContraction r x)
  have hd := coordinateDerivative_smooth_on_open f U hU N hf
  have hH (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : ContDiffOn ℝ N (fun x => H x r) U :=
    hd.comp (show ContDiffOn ℝ N (coordinateContraction (E:=E) r) U from
      (coordinateContraction (E:=E) r).contDiff.contDiffOn) (fun x hx => hcontract x hx r hr)
  let W : Set (ℝ×(ℝ×E)) := (fun w => (w.1*w.2.1,w.2.2)) ⁻¹' U
  have hmap : ContDiff ℝ N (fun w : ℝ×(ℝ×E) => (w.1*w.2.1,w.2.2)) := by fun_prop
  have hW : IsOpen W := hU.preimage hmap.continuous
  let G : ℝ×(ℝ×E) → ℝ := fun w => H w.2 w.1
  have hG : ContDiffOn ℝ N G W := by
    have ht : ContDiffOn ℝ N (fun w : ℝ×(ℝ×E) => (w.1*w.2.1,w.2.2)) W := hmap.contDiffOn
    have hc := hd.comp ht (fun _ h => h)
    apply hc.congr
    intro w hw
    simp only [G,H,coordinateContraction_apply,Function.comp_apply]
  have hmeas (j : ℕ) (hj : j ≤ N) (x : ℝ×E) (hx : x ∈ U) : AEStronglyMeasurable
      (fun r => iteratedFDeriv ℝ j (fun y => H y r) x) (volume.restrict (Icc (0:ℝ) 1)) := by
    have hc := continuousOn_fieldSlice_iteratedFDeriv_on_open G W hW hG hj
    have hm : Continuous (fun r : ℝ => (r,x)) := continuous_id.prodMk continuous_const
    have hc' := hc.comp hm.continuousOn (fun r hr => by
      simpa only [W,mem_preimage,coordinateContraction_apply] using hcontract x hx r hr)
    exact hc'.aestronglyMeasurable measurableSet_Icc
  have hbound (j : ℕ) (hj : j ≤ N) (x : ℝ×E) (hx : x ∈ U)
      (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      ‖iteratedFDeriv ℝ j (fun y => H y r) x‖ ≤ (K*Real.exp (D*‖x‖))^(j+1) := by
    have hrx := hcontract x hx r hr
    have hL := norm_coordinateContraction_le_one (E:=E) r hr
    have hnorm : ‖coordinateContraction r x‖ ≤ ‖x‖ :=
      ((coordinateContraction r).le_opNorm x).trans (by nlinarith [norm_nonneg x])
    apply (norm_iteratedFDeriv_comp_linear_on_open (coordinateDerivative f) U hU hd hj
      (coordinateContraction r) x hrx hL).trans
    apply (coordinateDerivative_jet_bound f U hU hf hj _ hrx).trans
    apply (hjets (j+1) (by omega) (by omega) _ hrx).trans
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hnorm hD)) (zero_le_one.trans hK)
  obtain ⟨hi,_,hb⟩ := compact_parameter_integral_smooth_exp_jets_on_open N H U hU hH hmeas
    K D (zero_le_one.trans hK) hD hbound
  have he : EqOn (smoothCoordinateSlope f) (fun x => ∫r in Icc (0:ℝ) 1,H x r) U := by
    intro x hx
    simpa only [smoothCoordinateSlopeIntegral,H,coordinateDerivative,coordinateContraction_apply] using
      smoothCoordinateSlope_eq_integral_on_open f U hU N hf hcontract hzero x hx
  refine ⟨hi.congr he,?_⟩
  intro j hj0 hj x hx
  have hev : smoothCoordinateSlope f =ᶠ[𝓝 x] (fun y => ∫r in Icc (0:ℝ) 1,H y r) :=
    mem_of_superset (hU.mem_nhds hx) (fun y hy => he hy)
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
  apply (hb j hj x hx).trans
  have hP : 1 ≤ K*Real.exp (D*‖x‖) := one_le_mul_of_one_le_of_one_le hK
    (Real.one_le_exp_iff.mpr (mul_nonneg hD (norm_nonneg _)))
  have hh := pow_le_pow_right₀ hP (show j+1 ≤ 2*j by omega)
  have hePow : (K*Real.exp (D*‖x‖))^2 = K^2*Real.exp ((2*D)*‖x‖) := by
    rw [mul_pow,←Real.exp_nat_mul]
    congr 2
    ring
  calc
    _ ≤ (K*Real.exp (D*‖x‖))^(2*j) := hh
    _ = ((K*Real.exp (D*‖x‖))^2)^j := pow_mul _ 2 j
    _ = _ := by rw [hePow]

end QuantitativePaper
