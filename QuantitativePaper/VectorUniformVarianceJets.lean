module
public import QuantitativePaper.VectorFiniteCells

@[expose] public section

/-! The positive-order Gaussian Cole--Hopf jet constants are independent of
the shift operator. Consequently finite-cell spatial/disorder jets are uniform
in the overlap time, including zero variance. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 400000

theorem gaussianShiftColeHopf_uniform_shift_jets {n : ℕ} (N : ℕ) (f : E→ℝ)
    (hf : ContDiff ℝ N f) (L : ℝ≥0) (hlip : LipschitzWith L f)
    (K : ℝ) (hK : 1 ≤ K)
    (hjets : ∀j,1 ≤ j → j ≤ N → ∀x,‖iteratedFDeriv ℝ j f x‖ ≤ K^j)
    (m : ℝ) :
    ∃D : ℝ,1 ≤ D ∧ ∀A : Field n→L[ℝ] E,∀j,1 ≤ j → j ≤ N → ∀x,
      ‖iteratedFDeriv ℝ j (gaussianShiftColeHopf A m f) x‖ ≤ D^j := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  by_cases hm : m=0
  · refine ⟨K,hK,?_⟩
    intro A j hj0 hj x
    have he : gaussianShiftColeHopf A m f=gaussianShiftAverage A f :=
      funext fun y => by simp [gaussianShiftColeHopf,hm]
    rw [he]
    exact norm_iteratedFDeriv_gaussianShiftAverage_le N j f hf L hlip K hK0 hjets A hj0 hj x
  · let B := fun j => |m⁻¹| * ((j.factorial : ℝ)*logJetCoefficient j*(gaussianDerivativePowerBound m K N)^j)
    refine ⟨finiteJetPowerBound B N,finiteJetPowerBound_ge_one B N,?_⟩
    intro A j hj0 hj x
    have hZ := contDiff_gaussianShiftPartition N f hf L hlip K hK0 hjets A m
    have hlog : ContDiff ℝ N (fun y => Real.log (gaussianShiftPartition A m f y)) :=
      hZ.log (fun y => (gaussianShiftPartition_pos f L hlip A m y).ne')
    have hfun : gaussianShiftColeHopf A m f=fun y => m⁻¹*Real.log (gaussianShiftPartition A m f y) :=
      funext fun y => by simp [gaussianShiftColeHopf,hm,div_eq_mul_inv,mul_comm]
    have hlogj := hlog.of_le (show (j : ℕ∞ω) ≤ N by norm_cast)
    have he : iteratedFDeriv ℝ j (gaussianShiftColeHopf A m f) x=
        m⁻¹ • iteratedFDeriv ℝ j (fun y => Real.log (gaussianShiftPartition A m f y)) x := by
      rw [hfun]
      exact iteratedFDeriv_const_smul_apply' (a := m⁻¹) (x := x) hlogj.contDiffAt
    rw [he,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_log_gaussianShiftPartition_le N j f hf L hlip K hK0 hjets A m hj0 hj x)
      (abs_nonneg _)).trans (finite_jet_bound_le_power B N j hj0 hj)

theorem vectorFiniteCellPotential_uniform_spatial_jets {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i N : ℕ) :
    ∃K : ℝ,1 ≤ K ∧ ∀q : ℝ,∀j,1 ≤ j → j ≤ N → ∀p : VectorParameter n,
      ‖iteratedFDeriv ℝ j (fun z : VectorParameter n =>
        vectorFiniteCellPotential s β t z.1 i q z.2) p‖ ≤ K^j := by
  obtain ⟨hSmooth,K,hK,hJets⟩ := vectorRecursion_joint_smooth_bounded_jets (n := n) s β t N (k+1-i)
  obtain ⟨D,hD,hBound⟩ := gaussianShiftColeHopf_uniform_shift_jets (n := n) N
    (fun p : VectorParameter n => vectorRecursion s β t p.1 (k+1-i) p.2) hSmooth
    (vectorJointLipschitzConstant n β t) (vectorRecursion_joint_lipschitz s β t (k+1-i))
    K hK hJets (s.m i)
  refine ⟨D,hD,?_⟩
  intro q j hj0 hj p
  let v := (1-t)*β^2*(s.q (i+1)-q)
  have he : gaussianShiftColeHopf (vectorJointShift n v) (s.m i)
      (fun p : VectorParameter n => vectorRecursion s β t p.1 (k+1-i) p.2)=
      fun p : VectorParameter n => vectorFiniteCellPotential s β t p.1 i q p.2 := by
    funext p
    exact gaussianShiftColeHopf_vectorRecursion s β t v (s.m i) (k+1-i) p
  exact he ▸ hBound (vectorJointShift n v) j hj0 hj p

end QuantitativePaper
