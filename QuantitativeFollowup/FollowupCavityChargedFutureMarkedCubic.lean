module
public import QuantitativeFollowup.FollowupCavityFutureMarkedCubic

@[expose] public section

/-! The charged strict-future cubic budget for the literal physical
conditional marks. Physical split equality is derived on the true free
Stieltjes measure; no continuity-at-atoms assumption is used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityChargedFutureMarkedTripleMoment (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T)) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
    (fun c => c.1 * (∫q : Paper.Overlap, if cavityProfileLevel s c.2.depth < q then
      (∫z, |cavityRecordedPairProduct s (trimRoot T) i l z.1 * cavitySpinOverlapDefect n q z.2.1 z.2.2|
        ∂anisotropicFutureVertexMarkedLaw D s a T c.2 q) else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))).sum

theorem cavityChargedFutureMarkedTripleMoment_le (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T)) :
    cavityChargedFutureMarkedTripleMoment D s a T i l ≤
      2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ) *
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a +
          finiteCascadeUnweightedBranchSum
            (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  have hi (F : Paper.Overlap → ℝ) : Integrable F (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) := by
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq]
    exact integrable_vectorProfileFreeMeasure s a F
  have hb : cavityChargedFutureMarkedTripleMoment D s a T i l ≤
      cavityChargedFutureGraftBranchBudget s a T (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a) := by
    unfold cavityChargedFutureMarkedTripleMoment cavityChargedFutureGraftBranchBudget
    apply List.sum_le_sum
    intro c hc
    apply mul_le_mul_of_nonneg_left _ (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
    apply integral_mono_ae (hi _) (hi _)
    have hd : c.2.depth ≤ k+2 := (c.2.depth_le).trans (by omega)
    filter_upwards [ae_cavityFiniteFutureDepth_level s a ha.1 has hq c.2.depth hd] with q hq'
    by_cases h : cavityProfileLevel s c.2.depth < q
    · simp only [ite_eq_left h]
      rw [finiteCascadeFutureVertexGraft_branchSum _ _ _ (cavityFiniteFutureDepth_le s c.2.depth q),hq' h]
      exact cavityFutureVertex_leaf_triple_cubic hn D s a hq T c.2 i l q (hq' h)
    · simp only [ite_eq_right h,le_refl]
  exact hb.trans (cavityChargedFutureGraftBranchBudget_le s a ha has hq T
    (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a)
    (fun q => (cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a q).1))

end QuantitativeFollowup
