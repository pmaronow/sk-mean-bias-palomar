module
public import QuantitativeFollowup.FiniteEuclideanPrekopa

@[expose] public section

/-! Prékopa on every finite Euclidean coordinate set, including the empty
set. The zero-dimensional case is the actual canonical Dirac volume. -/
noncomputable section
open MeasureTheory Set
namespace FourPapersCommon

theorem concaveOn_log_integral_exp_neg_all_finite_euclidean
    {ι : Type*} [Fintype ι] (S : Set ℝ) (hS : Convex ℝ S)
    (W : ℝ→EuclideanSpace ℝ ι→ℝ)
    (hW : ConvexOn ℝ (S ×ˢ univ) (Function.uncurry W))
    (hm : ∀t∈S,Measurable (W t))
    (hi : ∀t∈S,Integrable (fun x=>Real.exp (-W t x))) :
    ConcaveOn ℝ S (fun t=>Real.log (∫x,Real.exp (-W t x))) := by
  cases isEmpty_or_nonempty ι with
  | inr hne =>
    let _ := hne
    exact QuantitativeFollowup.concaveOn_log_integral_exp_neg_finite_euclidean S hS W hW hm hi
  | inl hempty =>
    let _ := hempty
    have hv : (volume : Measure (EuclideanSpace ℝ ι)) = Measure.dirac 0 := by
      rw [←(PiLp.volume_preserving_toLp ι).map_eq, Measure.volume_pi_eq_dirac (0 : ι→ℝ),
        Measure.map_dirac' (WithLp.measurable_toLp 2 _)]
      rfl
    have hc : ConvexOn ℝ S (fun t=>W t 0) := by
      refine ⟨hS,?_⟩
      intro t ht u hu a b ha hb hab
      have H := hW.2 (show (t,(0 : EuclideanSpace ℝ ι))∈S ×ˢ univ from ⟨ht,mem_univ _⟩)
        (show (u,(0 : EuclideanSpace ℝ ι))∈S ×ˢ univ from ⟨hu,mem_univ _⟩) ha hb hab
      simpa only [Function.uncurry,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
        smul_zero,zero_add,smul_eq_mul] using H
    have he : (fun t=>Real.log (∫x,Real.exp (-W t x))) = fun t=> -W t 0 := by
      funext t
      rw [hv, integral_dirac]
      exact Real.log_exp _
    rw [he]
    exact hc.neg

end FourPapersCommon
