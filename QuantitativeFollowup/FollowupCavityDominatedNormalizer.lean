module
public import QuantitativeFollowup.FollowupCavityDominatedPairIntegral

@[expose] public section

/-! The genuinely independent normalizer mark retains the cubic budget
for every measurable observable dominated by a pair of defects. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem independent_dominated_pair_product_cubic_bound {Ω Omega2 : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Omega2] (P : Measure Ω) (Q : Measure Omega2)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F x y : Ω → ℝ) (z : Omega2 → ℝ)
    (hF : Measurable F) (hx : Measurable x) (hy : Measurable y) (hz : Measurable z)
    (hxb : ∀ω, |x ω| ≤ 2) (hyb : ∀ω, |y ω| ≤ 2) (hzb : ∀σ, |z σ| ≤ 2)
    (hdom : ∀ω, |F ω| ≤ |x ω| * |y ω|) :
    |(∫ω, F ω ∂P)*(∫σ, z σ ∂Q)| ≤
      ((∫ω, |x ω|^3 ∂P)+(∫ω, |y ω|^3 ∂P)+(∫σ, |z σ|^3 ∂Q))/3 := by
  have hb (ω) : |x ω| * |y ω| ≤ 4 :=
    (mul_le_mul (hxb ω) (hyb ω) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hiF : Integrable F P := (integrable_const (4 : ℝ)).mono' hF.aestronglyMeasurable
    (.of_forall fun ω => by simpa only [Real.norm_eq_abs] using (hdom ω).trans (hb ω))
  have hi : Integrable (fun ω => |x ω| * |y ω|) P :=
    (integrable_const (4 : ℝ)).mono' (hx.abs.mul hy.abs).aestronglyMeasurable
      (.of_forall fun ω => by rw [Real.norm_of_nonneg (by positivity)]; exact hb ω)
  have hFabs : |∫ω, F ω ∂P| ≤ ∫ω, |F ω| ∂P := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := P) (f := F))
  have h1 : |∫ω, F ω ∂P| ≤ ∫ω, |x ω| * |y ω| ∂P :=
    hFabs.trans (integral_mono hiF.abs hi hdom)
  have h2 : |∫σ, z σ ∂Q| ≤ ∫σ, |z σ| ∂Q := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := Q) (f := z))
  have hh := independent_pair_product_cubic_bound P Q (fun ω => |x ω|) (fun ω => |y ω|)
    (fun σ => |z σ|) hx.abs hy.abs hz.abs
    (fun ω => by simpa only [abs_abs] using hxb ω)
    (fun ω => by simpa only [abs_abs] using hyb ω)
    (fun σ => by simpa only [abs_abs] using hzb σ)
  rw [abs_of_nonneg (mul_nonneg (integral_nonneg (fun ω => by positivity))
    (integral_nonneg (fun σ => abs_nonneg _)))] at hh
  simp only [abs_abs] at hh
  rw [abs_mul]
  exact (mul_le_mul h1 h2 (abs_nonneg _) (integral_nonneg (fun ω => by positivity))).trans hh

theorem cavityNormalizerPair_dominated_leaf_cubic (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (i l : Fin 2 → ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1) → ℝ) (hF : Measurable F)
    (hdom : ∀r, |F r| ≤ |cavityRecordedPairProduct s (trimRoot T) i l r|) (q : Paper.Overlap) :
    |(∫r,F r ∂anisotropicTrimmedRecordedTreeLaw D s a T)*
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
  have hh := independent_dominated_pair_product_cubic_bound P Q F x y z hF hx hy hz hxb hyb hzb (fun r => by simpa only [x,y,cavityRecordedPairProduct,abs_mul] using hdom r)
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
  change |(∫r,F r ∂P)*_|≤_ at hh ⊢
  change (∫r,|x r|^3 ∂P)≤_ at hb0
  change (∫r,|y r|^3 ∂P)≤_ at hb1
  linarith

theorem cavityNormalizer_dominated_leaf_cubic_budget (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1) → ℝ) (hF : Measurable F)
    (hdom : ∀r, |F r| ≤ |cavityRecordedPairProduct s (trimRoot T) i l r|) :
    |(∫r,F r ∂anisotropicTrimmedRecordedTreeLaw D s a T)*
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
  let H := fun q : Paper.Overlap => (∫r,F r
    ∂anisotropicTrimmedRecordedTreeLaw D s a T)*(∫z,cavitySpinOverlapDefect n q z.2.1 z.2.2
      ∂anisotropicFreshTerminalPairLaw D (Paper.parisiSchemeMeasure s) a q)
  have hH (q) : |H q|≤2*B+cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a q :=
    cavityNormalizerPair_dominated_leaf_cubic hn D s a hq T i l F hF hdom q
  have hmass : (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a).real univ ≤ 1 := by
    rw [measureReal_def,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith [ha.2])]
    linarith [ha.1]
  have hh := (norm_integral_le_integral_norm (μ:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) (f:=H)).trans
    (integral_mono (hi _) (hi _) (fun q => by simpa only [Real.norm_eq_abs] using hH q))
  rw [integral_add (integrable_const (2*B)) (hi _),integral_const,smul_eq_mul] at hh
  have hb : (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a).real univ*(2*B)≤2*B :=
    mul_le_of_le_one_left (by positivity) hmass
  unfold cavityNormalizerFreshDefect
  rw [←integral_const_mul]
  exact hh.trans (by
    simpa only [cavityThirdMoment, B, add_comm] using
      (add_le_add_right hb (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a)))

end QuantitativeFollowup
