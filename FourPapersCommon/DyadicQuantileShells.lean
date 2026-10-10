module
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! The genuine disjoint dyadic partition above a positive quantile cutoff. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 600000

def dyadicQuantileShell (s u : ℝ) (j : ℕ) : Set ℝ:=
  Ioo (0:ℝ) (1-s)∩Ico ((2:ℝ)^j*u-s) ((2:ℝ)^(j+1)*u-s)

theorem dyadicQuantileShell_ordConnected (s u : ℝ) (j : ℕ) :
    (dyadicQuantileShell s u j).OrdConnected:=
  ordConnected_Ioo.inter ordConnected_Ico

theorem dyadicQuantileShell_subset (s u : ℝ) (j : ℕ) :
    dyadicQuantileShell s u j⊆Ioo (0:ℝ) (1-s):=inter_subset_left

theorem dyadicQuantileShell_length_le (s u : ℝ) (hu : 0≤u) (j : ℕ) :
    volume.real (dyadicQuantileShell s u j)≤(2:ℝ)^j*u := by
  have he : ((2:ℝ)^(j+1)*u-s)-((2:ℝ)^j*u-s)=(2:ℝ)^j*u:=by
    rw [pow_succ]
    ring
  calc
    _≤volume.real (Ico ((2:ℝ)^j*u-s) ((2:ℝ)^(j+1)*u-s)):=
      measureReal_mono inter_subset_right (by rw [Real.volume_Ico];exact ENNReal.ofReal_ne_top)
    _=(2:ℝ)^j*u:=by
      rw [Real.volume_real_Ico,he,max_eq_left (by positivity)]

theorem dyadicQuantileShells_pairwiseDisjoint (s u : ℝ) (hu : 0<u) :
    Pairwise (fun i j : ℕ=>Disjoint (dyadicQuantileShell s u i) (dyadicQuantileShell s u j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hvi hvj
  rcases lt_or_gt_of_ne hij with hij'|hji'
  · have hp : (2:ℝ)^(i+1)≤(2:ℝ)^j:=pow_le_pow_right₀ (by norm_num) (by omega)
    have hh:=mul_le_mul_of_nonneg_right hp hu.le
    linarith [hvi.2.2,hvj.2.1]
  · have hp : (2:ℝ)^(j+1)≤(2:ℝ)^i:=pow_le_pow_right₀ (by norm_num) (by omega)
    have hh:=mul_le_mul_of_nonneg_right hp hu.le
    linarith [hvj.2.2,hvi.2.1]

theorem dyadicQuantileShells_cover (s u : ℝ) (hu : 0<u) :
    (⋃j : ℕ,dyadicQuantileShell s u j)=Ioo (0:ℝ) (1-s)∩Ici (u-s) := by
  ext v
  constructor
  · intro hv
    obtain ⟨j,hj⟩:=mem_iUnion.mp hv
    refine ⟨hj.1,?_⟩
    have hp : 1≤(2:ℝ)^j:=one_le_pow₀ (by norm_num)
    have hh:=mul_le_mul_of_nonneg_right hp hu.le
    change u-s≤v
    linarith [hj.2.1]
  · rintro ⟨hv,hvu⟩
    change u-s≤v at hvu
    have hx : 1≤(s+v)/u:=(le_div_iff₀ hu).mpr (by linarith)
    obtain ⟨j,hjL,hjR⟩:=exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
    apply mem_iUnion.mpr
    refine ⟨j,hv,?_⟩
    have hL:=(le_div_iff₀ hu).mp hjL
    have hR:=(div_lt_iff₀ hu).mp hjR
    constructor <;> linarith

end FourPapersCommon
