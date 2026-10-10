module
public import QuantitativePaper.VectorFiniteCellHeatIncrement
public import QuantitativePaper.VectorMildSource

@[expose] public section

/-! Exact finite-profile Duhamel increments using the actual atomic CDF.
Empty cells and endpoint atoms are retained by the clamped mesh. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def vectorFiniteTailHeatValue {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (q r : ℝ) (p : Couplings n×ℝ) (x : Field n) : ℝ :=
  ∫ z,vectorTailRecursion s β t r p (k+2)
    (fieldShift ((1-t)*β^2*(r-q)) x z) ∂fieldGaussian n

theorem vectorFiniteTailHeatValue_eq_cell {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (q r : ℝ) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    (hr : r∈Icc (s.q i) (s.q (i+1))) (x : Field n) :
    vectorFiniteTailHeatValue s β t q r p x=vectorFiniteCellHeatValue s β t p i q r x := by
  unfold vectorFiniteTailHeatValue vectorFiniteCellHeatValue
  rw [vectorTailRecursion_eq_finiteCell s β t r p i hi hr]

theorem vectorFiniteMildSource_eq_cell {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (q r : ℝ) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    (hr : r∈Ico (s.q i) (s.q (i+1))) (x : Field n) :
    vectorMildSource (Paper.parisiSchemeMeasure s) (vectorFiniteTailGradient s β t)
      ((1-t)*β^2) q r p x=(s.m i)*vectorFiniteCellGradientHeat s β t p i q r x := by
  have hr01 : r∈Icc (0 : ℝ) 1 :=
    ⟨(s.q_nonneg (by omega)).trans hr.1,hr.2.le.trans (s.q_le_one (by omega))⟩
  unfold vectorMildSource vectorGradientHeatAverage vectorFiniteCellGradientHeat
  rw [Paper.parisiCDF_scheme_cell s hi hr,projIcc_of_mem zero_le_one hr01]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    change ‖gradient (vectorTailRecursion s β t r p (k+2))
      (fieldShift ((1-t)*β^2*(r-q)) x z)‖^2=
      ‖gradient (vectorFiniteCellPotential s β t p i r)
        (fieldShift ((1-t)*β^2*(r-q)) x z)‖^2
    rw [vectorTailRecursion_eq_finiteCell s β t r p i hi ⟨hr.1,hr.2.le⟩])

theorem vectorFiniteMild_mesh_cell {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (p : Couplings n×ℝ)
    (i : ℕ) (hi : i≤k+1) (x : Field n) :
    vectorFiniteTailHeatValue s β t q (max (q : ℝ) (s.q (i+1))) p x-
      vectorFiniteTailHeatValue s β t q (max (q : ℝ) (s.q i)) p x=
      -((1-t)*β^2)/2*∫ r in max (q : ℝ) (s.q i)..max (q : ℝ) (s.q (i+1)),
        vectorMildSource (Paper.parisiSchemeMeasure s) (vectorFiniteTailGradient s β t)
          ((1-t)*β^2) q r p x := by
  let a := max (q : ℝ) (s.q i)
  let b := max (q : ℝ) (s.q (i+1))
  have hab : a≤b := max_le_max le_rfl (s.q_mono i hi)
  by_cases he : a=b
  · simp only [show max (q : ℝ) (s.q i)=max (q : ℝ) (s.q (i+1)) from he,
      sub_self,intervalIntegral.integral_same,mul_zero]
  have hlt : a<b := lt_of_le_of_ne hab he
  have hqnext : (q : ℝ)<s.q (i+1) := by
    by_contra hn
    have hn' : s.q (i+1)≤q := le_of_not_gt hn
    have hna : s.q i≤q := (s.q_mono i hi).trans hn'
    simp only [a,b,max_eq_left hn',max_eq_left hna] at hlt
    exact (lt_irrefl _) hlt
  have hb : b=s.q (i+1) := max_eq_right hqnext.le
  have haCell : a∈Icc (s.q i) (s.q (i+1)) :=
    ⟨le_max_right _ _,max_le hqnext.le (s.q_mono i hi)⟩
  have hbCell : b∈Icc (s.q i) (s.q (i+1)) := by rw [hb];exact ⟨s.q_mono i hi,le_rfl⟩
  have hcell := vectorFiniteCell_heat_increment s β t hβ ht p i hi q a b
    (le_max_left _ _) hab hb.le x
  change vectorFiniteTailHeatValue s β t q b p x-vectorFiniteTailHeatValue s β t q a p x=_
  rw [vectorFiniteTailHeatValue_eq_cell s β t q b p i hi hbCell,
    vectorFiniteTailHeatValue_eq_cell s β t q a p i hi haCell]
  have hint : (∫ r in a..b,vectorMildSource (Paper.parisiSchemeMeasure s)
      (vectorFiniteTailGradient s β t) ((1-t)*β^2) q r p x)=
      (s.m i)*∫ r in a..b,vectorFiniteCellGradientHeat s β t p i q r x := by
    have heq : EqOn (fun r => vectorMildSource (Paper.parisiSchemeMeasure s)
        (vectorFiniteTailGradient s β t) ((1-t)*β^2) q r p x)
        (fun r => (s.m i)*vectorFiniteCellGradientHeat s β t p i q r x) (uIoo a b) := by
      rw [uIoo_of_le hab]
      intro r hr
      exact vectorFiniteMildSource_eq_cell s β t q r p i hi
        ⟨haCell.1.trans hr.1.le,hr.2.trans_le hb.le⟩ x
    rw [intervalIntegral.integral_congr_uIoo heq,intervalIntegral.integral_const_mul]
  rw [hint,hcell]
  ring

end QuantitativePaper
