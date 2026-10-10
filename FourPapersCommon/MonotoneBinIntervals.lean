module
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! Actual interval geometry of level bins of a monotone function. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem monotone_level_bin_ordConnected (f : ℝ→ℝ) (hf : Monotone f)
    (I : Set ℝ) (hI : I.OrdConnected) (a b : ℝ) :
    (I∩f⁻¹' Ico a b).OrdConnected :=
  hI.inter (ordConnected_Ico.preimage_mono hf)

theorem ordConnected_ae_eq_open_interval (I : Set ℝ) (hI : I.OrdConnected)
    (hb : BddBelow I) (ha : BddAbove I) : I=ᵐ[volume]Ioo (sInf I) (sSup I) := by
  rcases I.eq_empty_or_nonempty with rfl|hne
  · simp
  have hin : Ioo (sInf I) (sSup I)⊆I :=
    (show IsConnected I from ⟨hne,hI.isPreconnected⟩).Ioo_csInf_csSup_subset hb ha
  have hout : I⊆Icc (sInf I) (sSup I):=subset_Icc_csInf_csSup hb ha
  filter_upwards [Ioo_ae_eq_Icc (a:=sInf I) (b:=sSup I) (μ:=volume)] with v hv
  change (v∈I)=(v∈Ioo (sInf I) (sSup I))
  apply propext
  constructor
  · intro h
    exact Eq.mp hv.symm (hout h)
  · intro h
    exact hin h

theorem volume_ordConnected_eq_endpoints (I : Set ℝ) (hI : I.OrdConnected)
    (hb : BddBelow I) (ha : BddAbove I) :
    volume.real I=max (sSup I-sInf I) 0 := by
  rw [Measure.real,measure_congr (ordConnected_ae_eq_open_interval I hI hb ha),Real.volume_Ioo,
    ENNReal.toReal_ofReal']

theorem ordConnected_inner_windows_subset (I : Set ℝ) (hI : I.OrdConnected)
    (hb : BddBelow I) (ha : BddAbove I) {v : ℝ} (hv : v∈Ioo (sInf I) (sSup I)) :
    Ioo (sInf I) v⊆I ∧ Ioo v (sSup I)⊆I := by
  have hne : I.Nonempty := by
    by_contra h
    have he : I=∅:=Set.not_nonempty_iff_eq_empty.mp h
    simp [he] at hv
  have hin : Ioo (sInf I) (sSup I)⊆I :=
    (show IsConnected I from ⟨hne,hI.isPreconnected⟩).Ioo_csInf_csSup_subset hb ha
  constructor
  · intro w hw
    exact hin ⟨hw.1,hw.2.trans hv.2⟩
  · intro w hw
    exact hin ⟨hv.1.trans hw.1,hw.2⟩

end FourPapersCommon
