module
public import QuantitativeFollowup.FollowupCavityOriginalVertexMarks
public import QuantitativeFollowup.FollowupCavityStreamingFuture

@[expose] public section

/-! Bounded measurable observables for the actual retained cavity law.
This justifies splitting the genuine five-term streaming expectation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

private def BM {Ω : Type} [MeasurableSpace Ω] (f : Ω→ℝ) : Prop :=
  Measurable f ∧ ∃ B, 0≤B ∧ ∀ x, |f x|≤B

private theorem bm_const {Ω : Type} [MeasurableSpace Ω] (c : ℝ) : BM (fun _ : Ω=>c) :=
  ⟨measurable_const,|c|,abs_nonneg _,fun _=>le_rfl⟩

private theorem bm_mul {Ω : Type} [MeasurableSpace Ω] {f g : Ω→ℝ}
    (hf : BM f) (hg : BM g) : BM (fun x=>f x*g x) := by
  obtain ⟨B,hB,hfb⟩:=hf.2
  obtain ⟨C,hC,hgb⟩:=hg.2
  refine ⟨hf.1.mul hg.1,B*C,mul_nonneg hB hC,fun x=>?_⟩
  rw [abs_mul]
  exact mul_le_mul (hfb x) (hgb x) (abs_nonneg _) hB

private theorem bm_sub {Ω : Type} [MeasurableSpace Ω] {f g : Ω→ℝ}
    (hf : BM f) (hg : BM g) : BM (fun x=>f x-g x) := by
  obtain ⟨B,hB,hfb⟩:=hf.2
  obtain ⟨C,hC,hgb⟩:=hg.2
  exact ⟨hf.1.sub hg.1,B+C,add_nonneg hB hC,fun x=>(abs_sub _ _).trans (add_le_add (hfb x) (hgb x))⟩

private theorem bm_div {Ω : Type} [MeasurableSpace Ω] {f : Ω→ℝ}
    (hf : BM f) (c : ℝ) : BM (fun x=>f x/c) := by
  simpa only [div_eq_mul_inv] using bm_mul hf (bm_const c⁻¹)

private theorem bm_list {Ω A : Type} [MeasurableSpace Ω] (xs : List A)
    (f : A→Ω→ℝ) (hf : ∀ a,BM (f a)) : BM (fun x=>(xs.map (fun a=>f a x)).sum) := by
  induction xs with
  | nil => simpa using bm_const (Ω:=Ω) 0
  | cons a xs ih =>
    obtain ⟨B,hB,hb⟩:=(hf a).2
    obtain ⟨C,hC,hc⟩:=ih.2
    refine ⟨?_,B+C,add_nonneg hB hC,fun x=>?_⟩
    · simp only [List.map_cons,List.sum_cons]
      convert! (hf a).1.add ih.1 using 1
    · simp only [List.map_cons,List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (hb x) (hc x))

private theorem bm_finsum {Ω A : Type} [MeasurableSpace Ω] [Fintype A]
    (f : A→Ω→ℝ) (hf : ∀a,BM (f a)) : BM (fun x=>∑a,f a x) := by
  classical
  simpa using bm_list (Finset.univ.toList) f hf

private theorem bm_select {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A] (g : A→Ω→ℝ) (hg : ∀a,BM (g a))
    (s : Ω→A) (hs : Measurable s) : BM (fun x=>g (s x) x) := by
  classical
  choose B hB hb using fun a=>(hg a).2
  refine ⟨?_,∑a,B a,Finset.sum_nonneg (fun a _=>hB a),fun x=>?_⟩
  · exact (measurable_from_prod_countable_left
      (f:=fun z : Ω×A=>g z.2 z.1) (fun a=>(hg a).1)).comp
      (measurable_id.prodMk hs)
  · exact (hb (s x) x).trans (Finset.single_le_sum (fun a _=>hB a) (Finset.mem_univ _))

private theorem BM.integrable {Ω : Type} [MeasurableSpace Ω] {f : Ω→ℝ}
    (hf : BM f) (P : Measure Ω) [IsFiniteMeasure P] : Integrable f P := by
  obtain ⟨B,hB,hb⟩:=hf.2
  apply (integrable_const B).mono' hf.1.aestronglyMeasurable
  exact .of_forall fun x=>by simpa only [Real.norm_eq_abs] using hb x

private theorem bm_mean (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T))
    (K : FiniteStateField (Configuration n)) : BM (anisotropicVertexMean D s v K) :=
  ⟨measurable_anisotropicVertexMean D s v K,‖K‖,norm_nonneg _,fun r=>anisotropicVertexMean_abs_le D s v K r⟩

private theorem bm_futureSquare (D : AnisotropicSpinModel n) (s : RSBScheme k)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T))
    (K : FiniteStateField (Configuration n)) (q : Paper.Overlap) :
    BM (fun r=>anisotropicVertexFutureSquare D s v K r q) := by
  refine ⟨?_,‖K‖*‖K‖,mul_nonneg (norm_nonneg _) (norm_nonneg _),fun r=>?_⟩
  · exact (finiteStateCascadePairMoment_measurable (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s) (cavityFiniteEnergyInput D s)
      (cavityFiniteFutureDepth s v.depth q) (v.depth-cavityFiniteFutureDepth s v.depth q) K K).comp v.measurable_field
  · exact finiteStateCascadePairMoment_abs_le _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _ _

private theorem bm_crossDefect (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    {T : FiniteTerminalGenealogy (k+2)} (v w : FiniteCascadeRecordVertex (trimRoot T))
    (q : ℝ) : BM (cavityCrossVertexConditionalDefect D s v w q) := by
  exact bm_sub (bm_div (bm_finsum _ (fun l=>bm_mul (bm_mean D s v _)
    (bm_mean D s w _))) n) (bm_mul (bm_mul (bm_const q) (bm_mean D s v _)) (bm_mean D s w _))

private theorem bm_futureDefect (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T))
    (q : Paper.Overlap) : BM (cavityFutureVertexConditionalDefect D s v q) :=
  bm_sub (bm_div (bm_finsum _ (fun l=>bm_futureSquare D s v _ q)) n)
    (bm_mul (bm_const (q:ℝ)) (bm_futureSquare D s v _ q))

private theorem bm_originalConditional (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) : BM (cavityOriginalVertexConditionalSum D s T v) := by
  apply bm_select (fun σ r=>((finiteCascadeTerminalVertices (trimRoot T) σ).map
    (fun c=>(∑l : Fin n,anisotropicCouplingFeature (cavityIncidentEdge l) c.2*
      anisotropicVertexMean D s v (anisotropicCouplingFeature (cavityIncidentEdge l)) r)/(n:ℝ)-
      cavityPhysicalCommonOverlap s (trimRoot T) c.1 v*Paper.spinSign (c.2 (Fin.last n))*
        anisotropicVertexMean D s v (cavityCoordinateFeature (Fin.last n)) r)).sum)
      (fun σ=>bm_list _ _ (fun c=>bm_sub
        (bm_div (bm_finsum _ (fun l=>bm_mul (bm_const _) (bm_mean D s v _))) n)
        (bm_mul (bm_const _) (bm_mean D s v _))))
  exact (measurable_finiteCascadeRecordTerminalSpins _).comp measurable_snd

private theorem bm_originalOriginal (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ) :
    BM (cavityRecordedOriginalOriginalDefect D s T b) := by
  apply bm_select (fun σ r=>((finiteCascadeTerminalVertices (trimRoot T) σ).map (fun c=>
    ((finiteCascadeTerminalVertices (trimRoot T) σ).map (fun d=>
      cavityRecordedMarkPairDefect D s T b r (.inl c) (.inl d))).sum)).sum)
      (fun σ=>bm_list _ _ (fun c=>bm_list _ _ (fun d=>by
        dsimp only [cavityRecordedMarkPairDefect,cavityRecordedMarkIncidentMean,
          cavityRecordedMarkEpsilonMean,cavityRecordedMarkVertex,Sum.elim_inl]
        exact bm_const _)))
  exact (measurable_finiteCascadeRecordTerminalSpins _).comp measurable_snd

private theorem bm_vertexVertex (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ) :
    BM (cavityRecordedVertexVertexDefect D s a T b) := by
  refine bm_list _ _ (fun c=>bm_list _ _ (fun d=>?_))
  simpa only [cavityRecordedMarkPairDefect_vertices] using bm_mul (bm_const (c.1*d.1))
    (bm_crossDefect (anisotropicReplaceVariance D (Fin.last n) b) s c.2 d.2
      (cavityPhysicalCommonOverlap s (trimRoot T) c.2 d.2))

private theorem bm_current (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ) :
    BM (cavityRecordedCurrentOverlapDefect D s a T b) :=
  bm_list _ _ (fun c=>bm_mul (bm_const _) (bm_crossDefect
    (anisotropicReplaceVariance D (Fin.last n) b) s c.2 c.2 (anisotropicVertexOverlap s c.2)))

private theorem bm_futureIntegral (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T)) :
    BM (fun r=>∫q : Paper.Overlap,if anisotropicVertexOverlap s v<q then
      cavityFutureVertexConditionalDefect D s v q r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) := by
  simp_rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq,
    integral_vectorProfileFreeMeasure s a has]
  apply bm_finsum
  intro i
  by_cases h:anisotropicVertexOverlap s v<vectorProfileAtom s i
  · simp only [ite_eq_left h]
    exact bm_mul (bm_const _) (bm_futureDefect D s v _)
  · simp only [ite_eq_right h,mul_zero]
    exact bm_const 0

theorem integrable_cavityCrossVertexConditionalDefect_mul
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (v w : FiniteCascadeRecordVertex (trimRoot T)) (q : ℝ)
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    Integrable (fun r=>F r*cavityCrossVertexConditionalDefect D s v w q r)
      (anisotropicTrimmedRecordedTreeLaw D s a T) :=
  (bm_mul ⟨hF,C,hC,hFb⟩ (bm_crossDefect D s v w q)).integrable _

theorem integrable_cavityFutureVertexConditionalDefect_mul
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T)) (q : Paper.Overlap)
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    Integrable (fun r=>F r*cavityFutureVertexConditionalDefect D s v q r)
      (anisotropicTrimmedRecordedTreeLaw D s a T) :=
  (bm_mul ⟨hF,C,hC,hFb⟩ (bm_futureDefect D s v q)).integrable _

theorem integrable_cavityOriginalVertexConditionalSum_mul
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    Integrable (fun r=>F r*cavityOriginalVertexConditionalSum D s T v r)
      (anisotropicTrimmedRecordedTreeLaw D s a T) :=
  (bm_mul ⟨hF,C,hC,hFb⟩ (bm_originalConditional D s T v)).integrable _

theorem integrable_cavityRecordedFiveTerms_mul
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    Integrable (fun r=>F r*cavityRecordedOriginalOriginalDefect D s T b r)
        (anisotropicTrimmedRecordedTreeLaw (anisotropicReplaceVariance D (Fin.last n) b) s a T) ∧
    Integrable (fun r=>F r*cavityRecordedOriginalVertexDefect D s a T b r)
        (anisotropicTrimmedRecordedTreeLaw (anisotropicReplaceVariance D (Fin.last n) b) s a T) ∧
    Integrable (fun r=>F r*cavityRecordedVertexVertexDefect D s a T b r)
        (anisotropicTrimmedRecordedTreeLaw (anisotropicReplaceVariance D (Fin.last n) b) s a T) ∧
    Integrable (fun r=>F r*cavityRecordedCurrentOverlapDefect D s a T b r)
        (anisotropicTrimmedRecordedTreeLaw (anisotropicReplaceVariance D (Fin.last n) b) s a T) ∧
    Integrable (fun r=>F r*cavityRecordedFutureOverlapDefect D s a T b r)
        (anisotropicTrimmedRecordedTreeLaw (anisotropicReplaceVariance D (Fin.last n) b) s a T) := by
  have hbm : BM F:=⟨hF,C,hC,hFb⟩
  have hTV : BM (cavityRecordedOriginalVertexDefect D s a T b) := by
    change BM (fun r=>cavityRecordedOriginalVertexDefect D s a T b r)
    simp_rw [cavityRecordedOriginalVertexDefect_eq_vertex_sum]
    exact bm_list _ _ (fun c=>bm_mul (bm_const _) (bm_originalConditional _ s T c.2))
  have hfuture : BM (cavityRecordedFutureOverlapDefect D s a T b) :=
    bm_list _ _ (fun c=>bm_mul (bm_const _) (bm_futureIntegral _ s a ha has hq c.2))
  exact ⟨(bm_mul hbm (bm_originalOriginal D s T b)).integrable _,
    (bm_mul hbm hTV).integrable _,(bm_mul hbm (bm_vertexVertex D s a T b)).integrable _,
    (bm_mul hbm (bm_current D s a T b)).integrable _,(bm_mul hbm hfuture).integrable _⟩

end QuantitativeFollowup
