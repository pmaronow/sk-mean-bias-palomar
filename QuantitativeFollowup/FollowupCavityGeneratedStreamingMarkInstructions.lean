module
public import QuantitativeFollowup.FollowupCavityGeneratedBranchMarks
public import QuantitativeFollowup.FollowupCavityGeneratedForestTemplateCubic

@[expose] public section

/-! Literal normalized attachment instructions. Free edge/fresh marks,
one coalesced atom-plus-CDF branch, CDF powers, and order restrictions
construct their actual measures. Their bounds depend only on attachment
and arity counts; Gaussian interpolation prefactors are kept separate. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def cavityGeneratedCDFPower {m : ℕ} (μ : Paper.ParisiMeasure) (i : Fin m)
    (r : ℕ) (h : CavityGeneratedHistory Paper.Overlap m) : ℝ≥0∞ :=
  (ENNReal.ofReal (Paper.parisiCDF μ (h i)))^r

theorem cavityGeneratedCDFPower_le_one {m : ℕ} (μ : Paper.ParisiMeasure)
    (i : Fin m) (r : ℕ) (h : CavityGeneratedHistory Paper.Overlap m) :
    cavityGeneratedCDFPower μ i r h ≤ 1 := by
  have hc : ENNReal.ofReal (Paper.parisiCDF μ (h i)) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (Paper.parisiCDF_le_one μ (h i))
  unfold cavityGeneratedCDFPower
  induction r with
  | zero => simp only [pow_zero, le_refl]
  | succ r ih =>
      rw [pow_succ]
      exact (mul_le_mul_right hc ((ENNReal.ofReal (Paper.parisiCDF μ (h i)))^r)).trans
        (by simpa only [mul_one] using ih)

theorem cavityGeneratedRootPower_le_one (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (r : ℕ) :
    (ENNReal.ofReal a)^r ≤ 1 := by
  have hc : ENNReal.ofReal a ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ha.2
  induction r with
  | zero => simp only [pow_zero, le_refl]
  | succ r ih =>
      rw [pow_succ]
      exact (mul_le_mul_right hc ((ENNReal.ofReal a)^r)).trans
        (by simpa only [mul_one] using ih)

inductive CavityGeneratedStreamingMarkHistory (μ : Paper.ParisiMeasure) : ℕ → Type
  | initial : CavityGeneratedStreamingMarkHistory μ 1
  | free {m : ℕ} (previous : CavityGeneratedStreamingMarkHistory μ m)
      (orderSet : Set (CavityGeneratedHistory Paper.Overlap m × Paper.Overlap)) :
      CavityGeneratedStreamingMarkHistory μ (m+1)
  | branch {m : ℕ} (previous : CavityGeneratedStreamingMarkHistory μ m)
      (i : Fin m) (arity : ℕ) (harity : 1 ≤ arity) :
      CavityGeneratedStreamingMarkHistory μ (m+1)
  | cdfPower {m : ℕ} (previous : CavityGeneratedStreamingMarkHistory μ m)
      (i : Fin m) (power : ℕ) : CavityGeneratedStreamingMarkHistory μ m
  | rootPower {m : ℕ} (previous : CavityGeneratedStreamingMarkHistory μ m)
      (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (power : ℕ) :
      CavityGeneratedStreamingMarkHistory μ m
  | order {m : ℕ} (previous : CavityGeneratedStreamingMarkHistory μ m)
      (orderSet : Set (CavityGeneratedHistory Paper.Overlap m)) :
      CavityGeneratedStreamingMarkHistory μ m

namespace CavityGeneratedStreamingMarkHistory
variable {μ : Paper.ParisiMeasure}

def program : {m : ℕ} → CavityGeneratedStreamingMarkHistory μ m →
    CavityGeneratedMarkProgram Paper.Overlap m
  | _, .initial => .initial
  | _, .free H E => .fresh H.program E
  | _, .branch H i l _ => cavityGeneratedBranchMarkProgram μ H.program i l
  | _, .cdfPower H i r => .attenuate H.program (cavityGeneratedCDFPower μ i r)
      (cavityGeneratedCDFPower_le_one μ i r)
  | _, .rootPower H a ha r => .attenuate H.program (fun _ => (ENNReal.ofReal a)^r)
      (fun _ => cavityGeneratedRootPower_le_one a ha r)
  | _, .order H E => .restrict H.program E

def attachmentCount : {m : ℕ} → CavityGeneratedStreamingMarkHistory μ m → ℕ
  | _, .initial => 0
  | _, .free H _ => H.attachmentCount+1
  | _, .branch H _ _ _ => H.attachmentCount+1
  | _, .cdfPower H _ _ => H.attachmentCount
  | _, .rootPower H _ _ _ => H.attachmentCount
  | _, .order H _ => H.attachmentCount

def maximumArity : {m : ℕ} → CavityGeneratedStreamingMarkHistory μ m → ℕ
  | _, .initial => 1
  | _, .free H _ => H.maximumArity
  | _, .branch H _ l _ => max l H.maximumArity
  | _, .cdfPower H _ _ => H.maximumArity
  | _, .rootPower H _ _ _ => H.maximumArity
  | _, .order H _ => H.maximumArity

theorem marks_eq_attachmentCount_succ {m : ℕ}
    (H : CavityGeneratedStreamingMarkHistory μ m) : m = H.attachmentCount+1 := by
  induction H with
  | initial => rfl
  | free H E ih => simp only [attachmentCount]; omega
  | branch H i l hl ih => simp only [attachmentCount]; omega
  | cdfPower H i r ih => exact ih
  | rootPower H a ha r ih => exact ih
  | order H E ih => exact ih

theorem maximumArity_pos {m : ℕ} (H : CavityGeneratedStreamingMarkHistory μ m) :
    1 ≤ H.maximumArity := by
  induction H with
  | initial => exact le_refl 1
  | free H E ih => exact ih
  | branch H i l hl ih => exact ih.trans (le_max_right _ _)
  | cdfPower H i r ih => exact ih
  | rootPower H a ha r ih => exact ih
  | order H E ih => exact ih

theorem budget_le_arity_power {m : ℕ} (H : CavityGeneratedStreamingMarkHistory μ m)
    (L : ℕ) (hL : H.maximumArity ≤ L) : H.program.budget ≤ L^H.attachmentCount := by
  induction H generalizing L with
  | initial => simp only [program, CavityGeneratedMarkProgram.budget, attachmentCount, pow_zero, le_refl]
  | free H E ih =>
      have hpos : 1 ≤ L := H.maximumArity_pos.trans hL
      exact (ih L hL).trans (pow_le_pow_right' hpos (Nat.le_succ _))
  | branch H i l hl ih =>
      change max l H.maximumArity ≤ L at hL
      simp only [program, attachmentCount, cavityGeneratedBranchMarkProgram_budget μ _ _ _ hl]
      rw [pow_succ]
      exact (Nat.mul_le_mul (le_of_max_le_left hL) (ih L (le_of_max_le_right hL))).trans_eq
        (Nat.mul_comm _ _)
  | cdfPower H i r ih => exact ih L hL
  | rootPower H a ha r ih => exact ih L hL
  | order H E ih => exact ih L hL

theorem threeDefects_count_bound {n m : ℕ}
    (hn : 0 < n) (D : AnisotropicSpinModel (n+1)) (a : ℝ) (ha : 0 ≤ a)
    (H : CavityGeneratedStreamingMarkHistory μ m)
    (W : CavityGeneratedForestClockTemplate m) (c : Fin 3 → Fin W.componentCount)
    (b e : (r : Fin 3) → ObservationLeaf (W.tree (c r)))
    (L r : ℕ) (hL : H.maximumArity ≤ L) (hr : H.attachmentCount ≤ 2*r) :
    (∫ h, cavityGeneratedForestThreeDefectMoment D μ a W.depth W.tree (W.clock h) c b e
      ∂(H.program.restrict W.orderSet).measure (parisiFreeMeasure μ a)) ≤
      (((2*r+1)*L^(2*r) : ℕ) : ℝ) * cavityThirdMoment D μ a := by
  have hpos : 1 ≤ L := H.maximumArity_pos.trans hL
  have hm : (m:ℝ) ≤ ((2*r+1:ℕ):ℝ) := by
    have hmn : m ≤ 2*r+1 := by
      rw [H.marks_eq_attachmentCount_succ]
      exact Nat.add_le_add_right hr 1
    exact_mod_cast hmn
  have hb : (H.program.budget:ℝ) ≤ ((L^(2*r):ℕ):ℝ) := by
    exact_mod_cast (H.budget_le_arity_power L hL).trans (pow_le_pow_right' hpos hr)
  have hc := mul_le_mul hm hb (Nat.cast_nonneg H.program.budget)
    (Nat.cast_nonneg (2*r+1))
  exact (cavityGeneratedForestTemplate_threeDefects_le hn D μ a ha H.program W c b e).trans
    (by simpa only [Nat.cast_mul] using
      mul_le_mul_of_nonneg_right hc (cavityThirdMoment_nonneg D μ a))

end CavityGeneratedStreamingMarkHistory

theorem followup_cavity_marked_history_three_defect_bound {n m : ℕ}
    (hn : 0 < n) (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1)
    (H : CavityGeneratedStreamingMarkHistory μ m)
    (W : CavityGeneratedForestClockTemplate m) (c : Fin 3 → Fin W.componentCount)
    (b e : (r : Fin 3) → ObservationLeaf (W.tree (c r)))
    (L r : ℕ) (hL : H.maximumArity ≤ L) (hr : H.attachmentCount ≤ 2*r) :
    (∫ h, cavityGeneratedForestThreeDefectMoment
      (followupCavitySpinModel n beta rho hbeta hrho u hu) μ a
      W.depth W.tree (W.clock h) c b e
      ∂(H.program.restrict W.orderSet).measure (parisiFreeMeasure μ a)) ≤
      (((2*r+1)*L^(2*r) : ℕ) : ℝ) *
        cavityThirdMoment (followupCavitySpinModel n beta rho hbeta hrho u hu) μ a :=
  H.threeDefects_count_bound hn _ a ha W c b e L r hL hr

end QuantitativeFollowup
