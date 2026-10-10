module
public import QuantitativeFollowup.FollowupCavityRecordedIntegrability
public import FourPapersCommon.ListRealIntegral

@[expose] public section

/-! The five non-normalizer terms of the finite physical streaming law.
Every mark below is sampled from its actual normalized continuation law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavityOriginalFreshExpectation (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>
    c.1*(∫z,F z.1*cavityOriginalVertexOverlapSum n s T c.2
      (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2) z.2
        ∂anisotropicSingleVertexMarkedLaw D s a T c.2))).sum

def cavityFreshFreshExpectation (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) : ℝ :=
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  (cs.map (fun c=>(cs.map (fun d=>c.1*d.1*
    (∫z,F z.1*cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.2 d.2) z.2.1 z.2.2
      ∂anisotropicCrossVertexMarkedLaw D s a T c.2 d.2))).sum)).sum

def cavityCurrentFreshExpectation (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>
    c.1*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2)*
      (∫z,F z.1*cavitySpinOverlapDefect n (anisotropicVertexOverlap s c.2) z.2.1 z.2.2
        ∂anisotropicCrossVertexMarkedLaw D s a T c.2 c.2))).sum

def cavityFutureFreshExpectation (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>
    c.1*(∫q : Paper.Overlap,if anisotropicVertexOverlap s c.2<q then
      (∫z,F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2
        ∂anisotropicFutureVertexMarkedLaw D s a T c.2 q) else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))).sum

theorem integral_cavityRecorded_originalFresh (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    (∫r,F r*cavityRecordedOriginalVertexDefect D s a T (D.variance (Fin.last n)) r
      ∂anisotropicTrimmedRecordedTreeLaw D s a T)=cavityOriginalFreshExpectation D s a T F := by
  simp_rw [cavityRecordedOriginalVertexDefect_eq_vertex_sum,anisotropicReplaceVariance_self]
  rw [integral_list_map_weighted_sum_real (anisotropicTrimmedRecordedTreeLaw D s a T)
    (finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T))
    (fun c : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>c.1)
    (fun c : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>cavityOriginalVertexConditionalSum D s T c.2)
    F (fun c : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>
      integrable_cavityOriginalVertexConditionalSum_mul D s a T c.2 F hF C hC hFb)]
  unfold cavityOriginalFreshExpectation
  simp_rw [integral_anisotropicSingleVertexMarkedLaw_original_overlap D s a T _ F hF C hC hFb]

theorem integral_cavityRecorded_freshFresh (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    (∫r,F r*cavityRecordedVertexVertexDefect D s a T (D.variance (Fin.last n)) r
      ∂anisotropicTrimmedRecordedTreeLaw D s a T)=cavityFreshFreshExpectation D s a T F := by
  classical
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  have hi (c d : ℝ×FiniteCascadeRecordVertex (trimRoot T)) :
      Integrable (fun r=>F r*cavityCrossVertexConditionalDefect D s c.2 d.2
        (cavityPhysicalCommonOverlap s (trimRoot T) c.2 d.2) r)
        (anisotropicTrimmedRecordedTreeLaw D s a T) :=
    integrable_cavityCrossVertexConditionalDefect_mul D s a T c.2 d.2 _ F hF C hC hFb
  have he (r) : F r*cavityRecordedVertexVertexDefect D s a T (D.variance (Fin.last n)) r=
      (cs.map (fun c=>(cs.map (fun d=>c.1*d.1*(F r*cavityCrossVertexConditionalDefect D s c.2 d.2
        (cavityPhysicalCommonOverlap s (trimRoot T) c.2 d.2) r))).sum)).sum := by
    unfold cavityRecordedVertexVertexDefect
    simp_rw [cavityRecordedMarkPairDefect_vertices,anisotropicReplaceVariance_self]
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro c _
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro d _
    ring
  simp_rw [he]
  rw [integral_list_map_sum_real _ cs _ (fun c=>integrable_list_map_sum_real _ cs _
    (fun d=>(hi c d).const_mul _))]
  simp_rw [integral_list_map_sum_real _ cs _ (fun d=>(hi _ d).const_mul _),integral_const_mul]
  unfold cavityFreshFreshExpectation
  simp_rw [integral_anisotropicCrossVertexMarkedLaw_overlapDefect D s a T _ _ _ F hF C hC hFb]
  rfl

theorem integral_cavityRecorded_currentFresh (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    (∫r,F r*cavityRecordedCurrentOverlapDefect D s a T (D.variance (Fin.last n)) r
      ∂anisotropicTrimmedRecordedTreeLaw D s a T)=cavityCurrentFreshExpectation D s a T F := by
  unfold cavityRecordedCurrentOverlapDefect
  simp_rw [anisotropicReplaceVariance_self]
  rw [integral_list_map_weighted_sum_real (anisotropicTrimmedRecordedTreeLaw D s a T)
    (finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T))
    (fun c : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>
      c.1*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2))
    (fun c : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>cavityCrossVertexConditionalDefect D s c.2 c.2
      (anisotropicVertexOverlap s c.2)) F
    (fun c : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>
      integrable_cavityCrossVertexConditionalDefect_mul D s a T c.2 c.2 _ F hF C hC hFb)]
  unfold cavityCurrentFreshExpectation
  simp_rw [integral_cavityRecordedCurrent_vertex_overlap D s a T _ F hF C hC hFb]

theorem integral_cavityRecorded_vertex_futureFresh (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    (∫r,F r*(∫q : Paper.Overlap,if anisotropicVertexOverlap s v<q then
      cavityFutureVertexConditionalDefect D s v q r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)
      ∂anisotropicTrimmedRecordedTreeLaw D s a T)=
      ∫q : Paper.Overlap,if anisotropicVertexOverlap s v<q then
        (∫z,F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2
          ∂anisotropicFutureVertexMarkedLaw D s a T v q) else 0
            ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
  classical
  simp_rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq,integral_vectorProfileFreeMeasure s a has]
  have he (r) : F r*(∑i,vectorPosteriorFeatureWeight s a i*
      (if anisotropicVertexOverlap s v<vectorProfileAtom s i then
        cavityFutureVertexConditionalDefect D s v (vectorProfileAtom s i) r else 0))=
      ∑i,vectorPosteriorFeatureWeight s a i*(if anisotropicVertexOverlap s v<vectorProfileAtom s i then
        F r*cavityFutureVertexConditionalDefect D s v (vectorProfileAtom s i) r else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _=>by
    by_cases h:anisotropicVertexOverlap s v<vectorProfileAtom s i
    · simp only [ite_eq_left h]
      exact (integrable_cavityFutureVertexConditionalDefect_mul D s a T v _ F hF C hC hFb).const_mul _
    · simp only [ite_eq_right h,mul_zero]
      exact integrable_zero _ _ _)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h:anisotropicVertexOverlap s v<vectorProfileAtom s i
  · simp only [ite_eq_left h,integral_const_mul]
    rw [integral_anisotropicFutureVertexMarkedLaw_overlapDefect D s a T v _ F hF C hC hFb]
  · simp only [ite_eq_right h,mul_zero,integral_zero]

theorem integral_cavityRecorded_futureFresh (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    (∫r,F r*cavityRecordedFutureOverlapDefect D s a T (D.variance (Fin.last n)) r
      ∂anisotropicTrimmedRecordedTreeLaw D s a T)=cavityFutureFreshExpectation D s a T F := by
  classical
  have hi (v : FiniteCascadeRecordVertex (trimRoot T)) :
      Integrable (fun r=>F r*(∫q : Paper.Overlap,if anisotropicVertexOverlap s v<q then
        cavityFutureVertexConditionalDefect D s v q r else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))
        (anisotropicTrimmedRecordedTreeLaw D s a T) := by
    simp_rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq,integral_vectorProfileFreeMeasure s a has,
      Finset.mul_sum]
    apply integrable_finsetSum
    intro i _
    by_cases h:anisotropicVertexOverlap s v<vectorProfileAtom s i
    · simp only [ite_eq_left h]
      convert! (integrable_cavityFutureVertexConditionalDefect_mul D s a T v
        (vectorProfileAtom s i) F hF C hC hFb).const_mul
        (vectorPosteriorFeatureWeight s a i) using 1
      funext r
      ring
    · simp only [ite_eq_right h,mul_zero]
      exact integrable_zero _ _ _
  unfold cavityRecordedFutureOverlapDefect
  simp_rw [anisotropicReplaceVariance_self]
  rw [integral_list_map_weighted_sum_real (anisotropicTrimmedRecordedTreeLaw D s a T)
    (finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T))
    (fun c : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>c.1)
    (fun c : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>fun r=>
      ∫q : Paper.Overlap,if anisotropicVertexOverlap s c.2<q then
        cavityFutureVertexConditionalDefect D s c.2 q r else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) F
    (fun c : ℝ×FiniteCascadeRecordVertex (trimRoot T)=>hi c.2)]
  unfold cavityFutureFreshExpectation
  simp_rw [integral_cavityRecorded_vertex_futureFresh D s a ha has hq T _ F hF C hC hFb]

theorem integral_cavityRecordedStreamingDefect_marked_five_terms
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    (∫r,F r*cavityRecordedStreamingDefect n D s a T (D.variance (Fin.last n)) r
      ∂anisotropicTrimmedRecordedTreeLaw D s a T)=
      (∫r,F r*cavityRecordedOriginalOriginalDefect D s T (D.variance (Fin.last n)) r
        ∂anisotropicTrimmedRecordedTreeLaw D s a T)-2*cavityOriginalFreshExpectation D s a T F+
          cavityFreshFreshExpectation D s a T F+cavityCurrentFreshExpectation D s a T F+
            cavityFutureFreshExpectation D s a T F := by
  obtain ⟨h1,h2,h3,h4,h5⟩:=integrable_cavityRecordedFiveTerms_mul D s a ha has hq T
    (D.variance (Fin.last n)) F hF C hC hFb
  simp only [anisotropicReplaceVariance_self] at h1 h2 h3 h4 h5
  have heF (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
      F r*cavityRecordedStreamingDefect n D s a T (D.variance (Fin.last n)) r=
        F r*cavityRecordedOriginalOriginalDefect D s T (D.variance (Fin.last n)) r-
        2*(F r*cavityRecordedOriginalVertexDefect D s a T (D.variance (Fin.last n)) r)+
        F r*cavityRecordedVertexVertexDefect D s a T (D.variance (Fin.last n)) r+
        F r*cavityRecordedCurrentOverlapDefect D s a T (D.variance (Fin.last n)) r+
        F r*cavityRecordedFutureOverlapDefect D s a T (D.variance (Fin.last n)) r := by
    rw [cavityRecordedStreamingDefect_five_terms D s a ha has hq T (D.variance (Fin.last n)) r]
    ring
  simp_rw [heF]
  have htwo := h2.const_mul 2
  have hA:=integral_add (((h1.sub htwo).add h3).add h4) h5
  have hB:=integral_add ((h1.sub htwo).add h3) h4
  have hC':=integral_add (h1.sub htwo) h3
  have hD:=integral_sub h1 htwo
  simp only [Pi.add_apply,Pi.sub_apply] at hA hB hC' hD
  rw [hA,hB,hC',hD]
  simp_rw [integral_const_mul]
  rw [integral_cavityRecorded_originalFresh D s a T F hF C hC hFb,
    integral_cavityRecorded_freshFresh D s a T F hF C hC hFb,
    integral_cavityRecorded_currentFresh D s a T F hF C hC hFb,
    integral_cavityRecorded_futureFresh D s a ha has hq T F hF C hC hFb]

end QuantitativeFollowup
