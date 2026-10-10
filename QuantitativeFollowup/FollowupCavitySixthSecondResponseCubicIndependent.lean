module
public import QuantitativeFollowup.FollowupCavityDominatedNormalizer
public import QuantitativeFollowup.FollowupCavityCrossPairDomination
public import QuantitativeFollowup.FollowupCavityFutureGraftSecondResponseGeometry

@[expose] public section

/-! Independent cubic Young bounds retain the actual marked-tree law and
an arbitrary independently sampled bounded scalar defect. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavitySixth_independent_pair_cubic {Ω : Type*} [MeasurableSpace Ω]
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (i l : Fin 2→ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hdom : ∀r,|F r|≤|cavityRecordedPairProduct s (trimRoot T) i l r|)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (z : Ω→ℝ)
    (hz : Measurable z) (hzb : ∀ω,|z ω|≤2) :
    |(∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*(∫ω,z ω∂Q)|≤
      2*finiteCascadeUnweightedBranchSum
        (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
        (trimRoot T)+(∫ω,|z ω|^3∂Q) := by
  let P:=anisotropicTrimmedRecordedTreeLaw D s a T
  let x:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)=>cavityRecordedLeafPairDefect s (trimRoot T) (i 0) (l 0) r.2
  let y:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)=>cavityRecordedLeafPairDefect s (trimRoot T) (i 1) (l 1) r.2
  have hx : Measurable x := (measurable_cavityRecordedLeafPairDefect (n:=n) (E:=FiniteStateField (Configuration (n+1))) s (trimRoot T) (i 0) (l 0)).comp measurable_snd
  have hy : Measurable y := (measurable_cavityRecordedLeafPairDefect (n:=n) (E:=FiniteStateField (Configuration (n+1))) s (trimRoot T) (i 1) (l 1)).comp measurable_snd
  have hh:=independent_dominated_pair_product_cubic_bound P Q F x y z hF hx hy hz
    (fun r=>cavityRecordedLeafPairDefect_abs_le_two s (trimRoot T) (i 0) (l 0) r.2)
    (fun r=>cavityRecordedLeafPairDefect_abs_le_two s (trimRoot T) (i 1) (l 1) r.2) hzb
    (fun r=>by simpa only [x,y,cavityRecordedPairProduct,abs_mul] using hdom r)
  have h0:=cavityRecordedLeafPairDefect_cube_le_branch hn D s a hq T (i 0) (l 0)
  have h1:=cavityRecordedLeafPairDefect_cube_le_branch hn D s a hq T (i 1) (l 1)
  have hB:=finiteCascadeUnweightedBranchSum_nonneg
    (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
    (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) (trimRoot T)
  have hz0 : 0≤∫ω,|z ω|^3∂Q:=integral_nonneg fun ω=>by positivity
  change (∫r,|x r|^3∂P)≤_ at h0
  change (∫r,|y r|^3∂P)≤_ at h1
  exact hh.trans (by linarith)

/-- The extra normalizer factor is an honest third independent defect. -/
theorem cavitySixth_independent_three_means {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2)) (i l : ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hdom : ∀r,|F r|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (P : Measure Ω) [IsProbabilityMeasure P] (y : Ω→ℝ) (hy : Measurable y) (hyb : ∀ω,|y ω|≤2)
    (Q : Measure Ω') [IsProbabilityMeasure Q] (z : Ω'→ℝ) (hz : Measurable z) (hzb : ∀ω,|z ω|≤2) :
    |(∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T)*(∫ω,y ω∂P)*(∫ω,z ω∂Q)|≤
      finiteCascadeUnweightedBranchSum
        (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
        (trimRoot T)+(∫ω,|y ω|^3∂P)+(∫ω,|z ω|^3∂Q) := by
  let R:=anisotropicTrimmedRecordedTreeLaw D s a T
  let x:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)=>cavityRecordedLeafPairDefect s (trimRoot T) i l r.2
  have hx : Measurable x:=(measurable_cavityRecordedLeafPairDefect (n:=n) (E:=FiniteStateField (Configuration (n+1))) s (trimRoot T) i l).comp measurable_snd
  have hh:=independent_dominated_pair_product_cubic_bound (R.prod P) Q
    (fun w=>F w.1*y w.2) (fun w=>x w.1) (fun w=>y w.2) z
    ((hF.comp measurable_fst).mul (hy.comp measurable_snd))
    (hx.comp measurable_fst) (hy.comp measurable_snd) hz
    (fun w=>cavityRecordedLeafPairDefect_abs_le_two s (trimRoot T) i l w.1.2)
    (fun w=>hyb w.2) hzb
    (fun w=>by rw [abs_mul];exact mul_le_mul_of_nonneg_right (hdom w.1) (abs_nonneg _))
  rw [integral_prod_mul] at hh
  have hf3 : (∫w : CavityPathRecordSpace (trimRoot T) (n+1)×Ω, |x w.1|^3∂ R.prod P)=
      ∫r,|x r|^3∂ R := by
    simpa only [probReal_univ,one_smul] using integral_fun_fst (μ:=R) (ν:=P) (fun r=>|x r|^3)
  have hy3 : (∫w : CavityPathRecordSpace (trimRoot T) (n+1)×Ω, |y w.2|^3∂ R.prod P)=
      ∫r,|y r|^3∂P := by
    simpa only [probReal_univ,one_smul] using integral_fun_snd (μ:=R) (ν:=P) (fun r=>|y r|^3)
  rw [hf3,hy3] at hh
  have hb:=cavityRecordedLeafPairDefect_cube_le_branch hn D s a hq T i l
  have hB:=finiteCascadeUnweightedBranchSum_nonneg
    (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
    (fun d=>(cavityCubicPairMoment_bounds D _ a _).1) (trimRoot T)
  have hy0 : 0≤∫ω,|y ω|^3∂P:=integral_nonneg fun ω=>by positivity
  have hz0 : 0≤∫ω,|z ω|^3∂Q:=integral_nonneg fun ω=>by positivity
  change (∫r,|x r|^3∂ R)≤_ at hb
  exact hh.trans (by linarith)

theorem cavitySixth_single_mark_independent_cubic {Ω : Type*} [MeasurableSpace Ω]
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (i l j : ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hdom : ∀r,|F r|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (z : Ω→ℝ) (hz : Measurable z) (hzb : ∀ω,|z ω|≤2) :
    |(∫r : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1),F r.1*cavitySpinOverlapDefect n
        (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v))
        (observationLeafSpin (trimRoot T) j r.1.2) r.2∂anisotropicSingleVertexMarkedLaw D s a T v)*
      (∫ω,z ω∂Q)|≤
      2*finiteCascadeUnweightedBranchSum
        (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
        (finiteCascadeVertexGraft v)+(∫ω,|z ω|^3∂Q) := by
  let e:=fun r : CavityPathRecordSpace (finiteCascadeVertexGraft v) (n+1)=>
    ((r.1,(finiteCascadeGraftRecordExtract v r.2).1),(finiteCascadeGraftRecordExtract v r.2).2)
  have he : Measurable e :=
    (measurable_fst.prodMk ((measurable_finiteCascadeGraftRecordExtract v).fst.comp measurable_snd)).prodMk
      ((measurable_finiteCascadeGraftRecordExtract v).snd.comp measurable_snd)
  let H:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)=>F r.1*cavitySpinOverlapDefect n
    (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v))
    (observationLeafSpin (trimRoot T) j r.1.2) r.2
  have hσ : Measurable (fun r : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)=>
      observationLeafSpin (trimRoot T) j r.1.2) :=
    (measurable_observationLeafSpin (E:=FiniteStateField (Configuration (n+1)))
      (S:=Configuration (n+1)) (trimRoot T) j).comp (measurable_snd.comp measurable_fst)
  let pair := fun r : CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)=>
    (observationLeafSpin (trimRoot T) j r.1.2,r.2)
  let d := fun p : Configuration (n+1)×Configuration (n+1)=>cavitySpinOverlapDefect n
    (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v)) p.1 p.2
  have hpair : Measurable pair := hσ.prodMk measurable_snd
  have hd : Measurable d := measurable_of_finite _
  have hdef : Measurable (d∘pair) := hd.comp hpair
  dsimp only [d,pair,Function.comp_def] at hdef
  have hH : Measurable H := (hF.comp measurable_fst).mul hdef
  have hm:=integral_map (μ:=anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeVertexGraft v)))
    he.aemeasurable hH.aestronglyMeasurable
  have hmap : (anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeVertexGraft v))).map e =
      anisotropicSingleVertexMarkedLaw D s a T v := anisotropicSingleVertexMarkedLaw_eq_graft D s a T v
  rw [hmap] at hm
  change |(∫r,H r∂anisotropicSingleVertexMarkedLaw D s a T v)*(∫ω,z ω∂Q)|≤_
  rw [hm]
  apply cavitySixth_independent_pair_cubic hn D s a hq (.advance (finiteCascadeVertexGraft v))
    ![finiteCascadeVertexGraftOldLeaf v i,finiteCascadeVertexGraftOldLeaf v j]
    ![finiteCascadeVertexGraftOldLeaf v l,finiteCascadeVertexGraftNewLeaf v] (H∘e) (hH.comp he) _ Q z hz hzb
  intro r
  dsimp only [H,e,Function.comp_def]
  simp only [cavityRecordedPairProduct,Matrix.cons_val_zero,Matrix.cons_val_one,cavityRecordedLeafPairDefect,
    finiteCascadeVertexGraftOldLeaf_commonLevel,finiteCascadeVertexGraftOldNewLeaf_commonLevel,
    finiteCascadeVertexGraftOldLeaf_spin,finiteCascadeVertexGraftNewLeaf_spin,abs_mul]
  exact mul_le_mul_of_nonneg_right (hdom (r.1,(finiteCascadeGraftRecordExtract v r.2).1)) (abs_nonneg _)

theorem cavitySixth_cross_mark_independent_cubic {Ω : Type*} [MeasurableSpace Ω]
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v w : FiniteCascadeRecordVertex (trimRoot T))
    (i l : ObservationLeaf (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (hdom : ∀r,|F r|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (z : Ω→ℝ) (hz : Measurable z) (hzb : ∀ω,|z ω|≤2) :
    |(∫r,F r.1*cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) v w) r.2.1 r.2.2
        ∂anisotropicCrossVertexMarkedLaw D s a T v w)*(∫ω,z ω∂Q)|≤
      2*finiteCascadeUnweightedBranchSum
        (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
        (finiteCascadeCrossVertexGraft v w)+(∫ω,|z ω|^3∂Q) := by
  let e:=fun r : CavityPathRecordSpace (finiteCascadeCrossVertexGraft v w) (n+1)=>
    ((r.1,(finiteCascadeCrossGraftExtract v w r.2).1),(finiteCascadeCrossGraftExtract v w r.2).2)
  have he : Measurable e :=
    (measurable_fst.prodMk ((measurable_finiteCascadeCrossGraftExtract v w).fst.comp measurable_snd)).prodMk
      ((measurable_finiteCascadeCrossGraftExtract v w).snd.comp measurable_snd)
  let H:=fun r : CavityPathRecordSpace (trimRoot T) (n+1)×(Configuration (n+1)×Configuration (n+1))=>
    F r.1*cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) v w) r.2.1 r.2.2
  have hH : Measurable H := (hF.comp measurable_fst).mul
    ((measurable_of_finite (fun p : Configuration (n+1)×Configuration (n+1)=>
      cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) v w) p.1 p.2)).comp measurable_snd)
  have hm:=integral_map (μ:=anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeCrossVertexGraft v w)))
    he.aemeasurable hH.aestronglyMeasurable
  have hmap : (anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeCrossVertexGraft v w))).map e =
      anisotropicCrossVertexMarkedLaw D s a T v w := anisotropicCrossVertexMarkedLaw_eq_graft D s a T v w
  rw [hmap] at hm
  rw [hm]
  apply cavitySixth_independent_pair_cubic hn D s a hq (.advance (finiteCascadeCrossVertexGraft v w))
    (cavityCrossGraftPairLeft v w i) (cavityCrossGraftPairRight v w l) (H∘e) (hH.comp he) _ Q z hz hzb
  intro r
  rw [cavityRecordedPairProduct_cross_graft]
  dsimp only [H,e,Function.comp_def]
  rw [cavityPhysicalCommonOverlap_eq_profileLevel,abs_mul,abs_mul]
  exact mul_le_mul_of_nonneg_right (hdom (r.1,(finiteCascadeCrossGraftExtract v w r.2).1)) (abs_nonneg _)

end QuantitativeFollowup
