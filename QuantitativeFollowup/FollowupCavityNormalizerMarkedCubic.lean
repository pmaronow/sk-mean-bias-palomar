module
public import QuantitativeFollowup.FollowupCavityIndependentCubic
public import QuantitativeFollowup.FollowupCavitySingleMarkedCubic
public import QuantitativeFollowup.FollowupCavitySixTermStreaming

@[expose] public section

/-! The independent two-fresh normalizer term obeys the actual cubic
budget, with its own independent disorder and true free-measure mass. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityRecordedLeafPairDefect_abs_le_two (s : RSBScheme k) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i l : ObservationLeaf T) {E : Type}
    (z : Records E (Configuration (n+1)) T) :
    |cavityRecordedLeafPairDefect s T i l z|≤2 :=
  cavitySpinOverlapDefect_abs_le_two n _ (cavityProfileLevel s _).property _ _

theorem cavityRecordedLeafPairDefect_cube_le_branch (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (i l : ObservationLeaf (trimRoot T)) :
    (∫r,|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|^3
      ∂anisotropicTrimmedRecordedTreeLaw D s a T) ≤
      finiteCascadeUnweightedBranchSum
        (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T) := by
  have hh := cavityTrimmedRecordedTripleDefectMoment_le_branch hn D s a hq T (fun _ => i) (fun _ => l)
  simpa only [cavityTrimmedRecordedTripleDefectMoment,abs_mul,pow_succ,pow_two,pow_zero,one_mul,mul_one] using hh

theorem cavityNormalizerPair_leaf_cubic (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (i l : Fin 2 → ObservationLeaf (trimRoot T)) (q : Paper.Overlap) :
    |(∫r,cavityRecordedPairProduct s (trimRoot T) i l r ∂anisotropicTrimmedRecordedTreeLaw D s a T)*
      (∫z,cavitySpinOverlapDefect n q z.2.1 z.2.2
        ∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q)| ≤
      2*finiteCascadeUnweightedBranchSum
        (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T) +
      cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a q := by
  let P := anisotropicTrimmedRecordedTreeLaw D s a T
  let Q := (anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q).snd
  let x := fun r : CavityPathRecordSpace (trimRoot T) (n+1) => cavityRecordedLeafPairDefect s (trimRoot T) (i 0) (l 0) r.2
  let y := fun r : CavityPathRecordSpace (trimRoot T) (n+1) => cavityRecordedLeafPairDefect s (trimRoot T) (i 1) (l 1) r.2
  let z := fun w : Configuration (n+1) × Configuration (n+1) => cavitySpinOverlapDefect n q w.1 w.2
  have hx : Measurable x := (measurable_cavityRecordedLeafPairDefect (n:=n) (E:=FiniteStateField (Configuration (n+1))) s (trimRoot T) (i 0) (l 0)).comp measurable_snd
  have hy : Measurable y := (measurable_cavityRecordedLeafPairDefect (n:=n) (E:=FiniteStateField (Configuration (n+1))) s (trimRoot T) (i 1) (l 1)).comp measurable_snd
  have hz : Measurable z := measurable_of_finite _
  have hxb := fun r : CavityPathRecordSpace (trimRoot T) (n+1) => cavityRecordedLeafPairDefect_abs_le_two (n:=n) s (trimRoot T) (i 0) (l 0) r.2
  have hyb := fun r : CavityPathRecordSpace (trimRoot T) (n+1) => cavityRecordedLeafPairDefect_abs_le_two (n:=n) s (trimRoot T) (i 1) (l 1) r.2
  have hzb := fun w : Configuration (n+1) × Configuration (n+1) => cavitySpinOverlapDefect_abs_le_two n q q.property w.1 w.2
  have hh := independent_pair_product_cubic_bound P Q x y z hx hy hz hxb hyb hzb
  have hcube : (∫w,|z w|^3 ∂Q)=cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a q := by
    rw [cavityCubicPairMoment_eq_fresh]
    simp only [Q,z,cavitySpinOverlapDefect_abs_eq_rest]
  have hmean : (∫w,z w ∂Q)=(∫w,cavitySpinOverlapDefect n q w.2.1 w.2.2
      ∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q) := by
    exact integral_map measurable_snd.aemeasurable hz.aestronglyMeasurable
  rw [hcube,hmean] at hh
  have hb0 := cavityRecordedLeafPairDefect_cube_le_branch hn D s a hq T (i 0) (l 0)
  have hb1 := cavityRecordedLeafPairDefect_cube_le_branch hn D s a hq T (i 1) (l 1)
  have hB := finiteCascadeUnweightedBranchSum_nonneg
    (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
    (fun d => (cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a _).1) (trimRoot T)
  have hχ := (cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a q).1
  change |(∫r,x r*y r ∂P)*_|≤_ at hh ⊢
  change (∫r,|x r|^3 ∂P)≤_ at hb0
  change (∫r,|y r|^3 ∂P)≤_ at hb1
  linarith

theorem cavityNormalizer_leaf_cubic_budget (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T)) :
    |(∫r,cavityRecordedPairProduct s (trimRoot T) i l r ∂anisotropicTrimmedRecordedTreeLaw D s a T)*
      cavityNormalizerFreshDefect D (Paper.parisiSchemeMeasure s) a| ≤
      2*finiteCascadeUnweightedBranchSum
        (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T) +
      cavityThirdMoment D (Paper.parisiSchemeMeasure s) a := by
  let B := finiteCascadeUnweightedBranchSum
    (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)
  have hB : 0≤B := finiteCascadeUnweightedBranchSum_nonneg _
    (fun d => (cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a _).1) _
  have hi (F : Paper.Overlap → ℝ) : Integrable F (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) := by
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha.1 has hq]
    exact integrable_vectorProfileFreeMeasure s a F
  let F := fun q : Paper.Overlap => (∫r,cavityRecordedPairProduct s (trimRoot T) i l r
    ∂anisotropicTrimmedRecordedTreeLaw D s a T)*(∫z,cavitySpinOverlapDefect n q z.2.1 z.2.2
      ∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q)
  have hF (q) : |F q|≤2*B+cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a q :=
    cavityNormalizerPair_leaf_cubic hn D s a hq T i l q
  have hmass : (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a).real univ ≤ 1 := by
    rw [measureReal_def,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith [ha.2])]
    linarith [ha.1]
  have hh := (norm_integral_le_integral_norm (μ:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) (f:=F)).trans
    (integral_mono (hi _) (hi _) (fun q => by simpa only [Real.norm_eq_abs] using hF q))
  rw [integral_add (integrable_const (2*B)) (hi _),integral_const,smul_eq_mul] at hh
  have hb : (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a).real univ*(2*B)≤2*B :=
    mul_le_of_le_one_left (by positivity) hmass
  unfold cavityNormalizerFreshDefect
  rw [←integral_const_mul]
  exact hh.trans (by
    simpa only [cavityThirdMoment, B, add_comm] using
      (add_le_add_right hb (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a)))

end QuantitativeFollowup
