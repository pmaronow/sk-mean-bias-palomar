module
public import Mathlib.Tactic

@[expose] public section

/-! Exact nonnegative three-piece realization of an affine covariance cell.
The two base pieces sum to a constant and the active piece carries either
sign of the covariance derivative. -/
noncomputable section
namespace FourPapersCommon
set_option maxHeartbeats 900000

def signedAffineCellTime (δ u : ℝ) : ℝ := (u+δ)/(2*δ)

def signedAffineCellScale (p t : ℝ) : ℝ := if 0≤p then t else 1-t

theorem signedAffineCellTime_mem_unit {δ u : ℝ} (hδ : 0<δ)
    (hu : |u|≤δ) : signedAffineCellTime δ u∈Set.Icc (0:ℝ) 1 := by
  unfold signedAffineCellTime
  have hh := abs_le.mp hu
  exact ⟨div_nonneg (by linarith [hh.1]) (by positivity),
    (div_le_one (by positivity : 0<2*δ)).mpr (by linarith [hh.2])⟩

theorem signedAffineCellTime_mem_interior {δ u : ℝ} (hδ : 0<δ)
    (hu : |u|<δ) : signedAffineCellTime δ u∈Set.Ioo (0:ℝ) 1 := by
  unfold signedAffineCellTime
  have hh := abs_lt.mp hu
  exact ⟨div_pos (by linarith [hh.1]) (by positivity),
    (div_lt_one (by positivity : 0<2*δ)).mpr (by linarith [hh.2])⟩

theorem signedAffineCellScale_mem_unit (p : ℝ) {t : ℝ} (ht : t∈Set.Icc (0:ℝ) 1) :
    signedAffineCellScale p t∈Set.Icc (0:ℝ) 1 := by
  unfold signedAffineCellScale
  split_ifs
  · exact ht
  · constructor <;> linarith [ht.1,ht.2]

theorem signedAffineCellSplitting_sum (Δ p δ u : ℝ) (hδ : δ≠0) :
    signedAffineCellScale p (signedAffineCellTime δ u)*(2*δ*|p|)+
      signedAffineCellTime δ u*(Δ-δ*|p|)+
      (1-signedAffineCellTime δ u)*(Δ-δ*|p|)=Δ+u*p := by
  unfold signedAffineCellScale signedAffineCellTime
  by_cases hp : 0≤p
  · rw [ite_eq_left hp,abs_of_nonneg hp]
    field_simp [hδ]
    ring
  · rw [ite_eq_right hp,abs_of_neg (lt_of_not_ge hp)]
    field_simp [hδ]
    ring

theorem signedAffineCellSplitting_order (Δ p δ u : ℝ) (hδ : 0<δ)
    (hu : |u|≤δ) (hbase : 0≤Δ-δ*|p|) :
    0≤signedAffineCellScale p (signedAffineCellTime δ u)*(2*δ*|p|) ∧
      0≤signedAffineCellTime δ u*(Δ-δ*|p|) ∧
      0≤(1-signedAffineCellTime δ u)*(Δ-δ*|p|) := by
  have ht := signedAffineCellTime_mem_unit hδ hu
  have hp := signedAffineCellScale_mem_unit p ht
  exact ⟨mul_nonneg hp.1 (by positivity),mul_nonneg ht.1 hbase,
    mul_nonneg (by linarith [ht.2]) hbase⟩

end FourPapersCommon
