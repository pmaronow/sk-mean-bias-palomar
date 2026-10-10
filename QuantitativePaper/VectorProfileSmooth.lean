module
public import QuantitativePaper.VectorProfileStepRepresentation
public import QuantitativePaper.LocalExponentialJetClosure
public import QuantitativePaper.VectorMagnetizationSmooth

@[expose] public section

/-! Actual joint profile, disorder and field regularity of finite Parisi
recursions. Every Gaussian dominance, mass inverse and derivative-growth
bound is discharged for the physical affine profile. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2000000

theorem vectorProfileJointFunction_smooth_exp_jets_on_cylinder {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) (N j : ℕ)
    (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ContDiffOn ℝ N (vectorProfileJointFunction (n:=n) s₀ s₁ β t j)
      {z : ℝ×VectorParameter n | z.1 ∈ Ioo a b} ∧
      ∃ K D : ℝ, 1 ≤ K ∧ 1 ≤ D ∧ ∀ r, 1 ≤ r → r ≤ N →
        ∀ x : ℝ×VectorParameter n, x.1 ∈ Ioo a b →
          ‖iteratedFDeriv ℝ r (vectorProfileJointFunction s₀ s₁ β t j) x‖ ≤
            (K*Real.exp (D*‖x‖))^r := by
  let U : Set (ℝ×VectorParameter n) := {z | z.1 ∈ Ioo a b}
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_fst
  have hphys (x : ℝ×VectorParameter n) (hx : x ∈ U) : x.1 ∈ Icc (0:ℝ) 1 :=
    ⟨(ha.trans hx.1).le, (hx.2.trans hb).le⟩
  induction j with
  | zero =>
    have hf := (boundedPositiveJets_vectorRecursion_joint (n:=n) s₀ β t 0).comp_linear
      (ContinuousLinearMap.snd ℝ ℝ (VectorParameter n))
    have hf' : BoundedPositiveJets (vectorProfileJointFunction (n:=n) s₀ s₁ β t 0) := by
      exact hf
    obtain ⟨K, hK, hJets⟩ := boundedPositiveJets_power_bound _ hf' N
    refine ⟨(hf'.1.of_le (by simp)).contDiffOn, K, 1, hK, le_rfl, ?_⟩
    intro r hr0 hr x _
    exact (hJets r hr0 hr x).trans (pow_le_pow_left₀ (zero_le_one.trans hK)
      (le_mul_of_one_le_right (zero_le_one.trans hK) (Real.one_le_exp_iff.mpr (by positivity))) r)
  | succ j ih =>
    obtain ⟨hf, K, D, hK, hD, hfj⟩ := ih
    let f := vectorProfileJointFunction (n:=n) s₀ s₁ β t j
    let m := vectorProfileStepMass (n:=n) s₀ s₁ j
    let A := vectorProfileJointShift n (vectorProfileStepVariance s₀ β t j)
    have hshift : ∀ x ∈ U, ∀ z, x+A z ∈ U := by
      intro x hx z
      rw [vectorProfileJointShift_add]
      exact hx
    obtain ⟨B, L, hB, hL, hvalue⟩ := vectorProfileJointFunction_linear_growth (n:=n) s₀ s₁ β t ht j
    have hv : ∀ x ∈ U, |f x| ≤ B+L*‖x‖ := fun x hx => hvalue x (hphys x hx)
    rcases vectorProfileMass_zero_or_pos s₀ s₁ (k+1-j) (Nat.sub_le _ _) with hm0|hmpos
    · obtain ⟨C, R, hC, hR, henv⟩ := exists_all_order_power_envelope N f U B L K D hB hL hK
        (zero_le_one.trans hD) hv hfj
      obtain ⟨hs, C', hC', hjets⟩ := gaussianShiftAverage_smooth_exp_jets_on_open N f U hU hf A hshift
        C R hC (zero_le_one.trans hR) henv
      have he : vectorProfileJointFunction (n:=n) s₀ s₁ β t (j+1)=gaussianShiftAverage A f := by
        funext x
        rw [vectorProfileJointFunction_step_eq]
        simp only [vectorProfileStepMass, hm0, ite_true]
        rfl
      rw [← he] at hs hjets
      exact ⟨hs, C', 2*R, hC', by linarith, hjets⟩
    · have hmp : ∀ x ∈ U, 0 < m x := fun x hx =>
        hmpos x.1 ⟨ha.trans hx.1, hx.2.trans hb⟩
      have hmSmooth : ContDiffOn ℝ N m U :=
        (contDiff_vectorProfileMass s₀ s₁ (k+1-j) N).comp contDiff_fst |>.contDiffOn
      obtain ⟨M, hM, hmass⟩ := exists_vectorProfileMass_cylinder_bound (n:=n) s₀ s₁ (k+1-j) N a b
      have hmJets : ∀ r, r ≤ N → ∀ x ∈ U, ‖iteratedFDeriv ℝ r m x‖ ≤ M :=
        fun r hr x hx => hmass r hr x ⟨hx.1.le, hx.2.le⟩
      obtain ⟨hG, KG, DG, hKG, hDG, hGj⟩ := mul_smooth_exp_jets_on_open N f m U hU hf hmSmooth
        B L K D M hB hL hK (zero_le_one.trans hD) hM hv hfj hmJets
      let G := fun x => m x*f x
      have hGv : ∀ x ∈ U, G x ≤ B+L*‖x‖ := by
        intro x hx
        have hm := vectorProfileMass_mem_unit s₀ s₁ (k+1-j) (Nat.sub_le _ _) x.1 (hphys x hx)
        change 0 ≤ m x ∧ m x ≤ 1 at hm
        have habs : |G x| ≤ |f x| := by
          dsimp only [G]
          rw [abs_mul, abs_of_nonneg hm.1]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hm.2 (abs_nonneg (f x))
        exact (le_abs_self (G x)).trans (habs.trans (hv x hx))
      have hGlip : ∀ x ∈ U, ∀ z, |G (x+A z)-G x| ≤
          ((vectorJointLipschitzConstant n β t:ℝ)*‖vectorJointShift n (vectorProfileStepVariance s₀ β t j)‖)*‖z‖ :=
        fun x hx z => vectorProfileStepExponent_shift_lipschitz s₀ s₁ β t _ j x (hphys x hx) z
      obtain ⟨hLog, KL, hKL, hLj⟩ := log_gaussianShiftPartition_smooth_exp_jets N G U hU hG A hshift
        B L KG DG _ hL (zero_le_one.trans hKG) (zero_le_one.trans hDG) hGv hGj hGlip
      let Z := fun x => Real.log (gaussianShiftPartition A 1 G x)
      obtain ⟨B', L', hB', hL', hvalue'⟩ := vectorProfileJointFunction_linear_growth (n:=n) s₀ s₁ β t ht (j+1)
      have hZv : ∀ x ∈ U, |Z x| ≤ B'+L'*‖x‖ := by
        intro x hx
        have hm := vectorProfileMass_mem_unit s₀ s₁ (k+1-j) (Nat.sub_le _ _) x.1 (hphys x hx)
        change |Real.log (gaussianShiftPartition
          (vectorProfileJointShift n (vectorProfileStepVariance s₀ β t j)) 1
          (fun y => vectorProfileStepMass s₀ s₁ j y * vectorProfileJointFunction s₀ s₁ β t j y) x)|
          ≤ B'+L'*‖x‖
        rw [log_vectorProfileStepPartition_eq s₀ s₁ β t j x (hmp x hx).ne']
        change 0 ≤ vectorProfileStepMass s₀ s₁ j x ∧ vectorProfileStepMass s₀ s₁ j x ≤ 1 at hm
        rw [abs_mul, abs_of_nonneg hm.1]
        exact (mul_le_mul_of_nonneg_right hm.2 (abs_nonneg _)).trans
          (by simpa only [one_mul] using hvalue' x (hphys x hx))
      have hInv : ContDiffOn ℝ N (fun x => (m x)⁻¹) U := hmSmooth.inv (fun x hx => (hmp x hx).ne')
      obtain ⟨MI, hMI, hinv⟩ := exists_vectorProfileMass_inverse_cylinder_bound (n:=n) s₀ s₁
        (k+1-j) N hmpos a b ha hb
      have hiJets : ∀ r, r ≤ N → ∀ x ∈ U, ‖iteratedFDeriv ℝ r (fun x => (m x)⁻¹) x‖ ≤ MI :=
        fun r hr x hx => hinv r hr x ⟨hx.1.le, hx.2.le⟩
      obtain ⟨hs, C, R, hC, hR, hjets⟩ := mul_smooth_exp_jets_on_open N Z (fun x => (m x)⁻¹) U hU
        hLog hInv B' L' KL DG MI hB' hL' hKL (zero_le_one.trans hDG) hMI hZv hLj hiJets
      have he : EqOn (vectorProfileJointFunction (n:=n) s₀ s₁ β t (j+1)) (fun x => (m x)⁻¹*Z x) U := by
        intro x hx
        rw [vectorProfileJointFunction_step_eq, if_neg (hmp x hx).ne']
      refine ⟨hs.congr he, C, R, hC, hR, ?_⟩
      intro r hr0 hr x hx
      have hev : vectorProfileJointFunction (n:=n) s₀ s₁ β t (j+1) =ᶠ[𝓝 x]
          fun x => (m x)⁻¹*Z x := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact he hy
      rw [(hev.iteratedFDeriv ℝ r).eq_of_nhds]
      exact hjets r hr0 hr x hx

end QuantitativePaper
