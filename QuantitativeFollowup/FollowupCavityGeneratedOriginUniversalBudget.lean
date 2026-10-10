module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionKernel
public import Mathlib.Algebra.Module.NatInt

@[expose] public section

/-! A common old-coordinate majorant permits one aggregate budget over
different forest charts. Fork multiplicities remain actual; replacing the
static lists by all old coordinates loses only a count-dependent factor. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedUniversalForkIndex (K m : ℕ) :
    Fin (Fintype.card (Fin (K-1) × Fin m)) → Fin m :=
  fun i => ((Fintype.equivFin (Fin (K-1) × Fin m)).symm i).2

theorem cavityGeneratedUniversalForkIndex_count (K m : ℕ) :
    Fintype.card (Fin (K-1) × Fin m) = (K-1)*m := by simp

theorem cavityGeneratedUniversalForkIndex_sum (K : ℕ)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    (∑i : Fin (Fintype.card (Fin (K-1) × Fin m)),
      Measure.dirac (h (cavityGeneratedUniversalForkIndex K m i))) =
      (K-1) • (∑j : Fin m, Measure.dirac (h j)) := by
  classical
  change (∑i : Fin (Fintype.card (Fin (K-1) × Fin m)),
    (fun z : Fin (K-1) × Fin m => Measure.dirac (h z.2))
      ((Fintype.equivFin (Fin (K-1) × Fin m)).symm i)) = _
  calc
    _ = ∑z : Fin (K-1) × Fin m, Measure.dirac (h z.2) :=
      Fintype.sum_equiv (Fintype.equivFin (Fin (K-1) × Fin m)).symm _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]

theorem cavityGeneratedForkDiracList_le_all_marks
    (L : List (Fin m)) (h : CavityGeneratedHistory Paper.Overlap m) :
    (L.map (fun i => Measure.dirac (h i))).sum ≤
      L.length • (∑j : Fin m, Measure.dirac (h j)) := by
  classical
  induction L with
  | nil => simp
  | cons i L ih =>
      have hi : Measure.dirac (h i) ≤ ∑j : Fin m, Measure.dirac (h j) :=
        Finset.single_le_sum (f := fun j : Fin m => Measure.dirac (h j))
          (fun j _ => bot_le) (Finset.mem_univ i)
      simpa only [List.map_cons,List.sum_cons,List.length_cons,succ_nsmul,add_comm]
        using add_le_add hi ih

theorem cavityGeneratedOriginSelectionKernel_clock_universal_domination
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (K : ℕ)
    (hK : FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) ≤ K)
    (h : CavityGeneratedHistory Paper.Overlap m) (hh : h ∈ W.clockTemplate.orderSet) :
    (cavityGeneratedOriginSelectionKernel μ a W c h).map
      (fun g => cavityGeneratedOriginSelectionClock W c (h,g)) ≤
      (K : ℝ≥0∞) • parisiFreeMeasure μ a +
        ∑i : Fin (Fintype.card (Fin (K-1) × Fin m)),
          Measure.dirac (h (cavityGeneratedUniversalForkIndex K m i)) := by
  classical
  have hd := cavityGeneratedOriginSelectionKernel_clock_domination μ a ha hμ W c h hh
  have hf : (cavityGeneratedOriginForkMarks W c).length ≤ K-1 := by
    have hc := cavityGeneratedOriginForkMarks_count W c
    omega
  have hl := cavityGeneratedForkDiracList_le_all_marks (cavityGeneratedOriginForkMarks W c) h
  have he (f : Fin m → Measure Paper.Overlap) :
      ((cavityGeneratedOriginForkMarks W c).map f).sum =
        ∑i : Fin (cavityGeneratedOriginForkMarks W c).length,
          f ((cavityGeneratedOriginForkMarks W c).get i) := by
    have hx := congrArg (fun L : List (Fin m) => (L.map f).sum)
      (List.ofFn_get (cavityGeneratedOriginForkMarks W c))
    simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_def] using hx.symm
  rw [he] at hl
  apply hd.trans
  apply add_le_add
  · apply cavityGenerated_smul_mono
    exact_mod_cast hK
  · rw [cavityGeneratedUniversalForkIndex_sum]
    exact hl.trans (nsmul_le_nsmul_left bot_le hf)

end QuantitativeFollowup
