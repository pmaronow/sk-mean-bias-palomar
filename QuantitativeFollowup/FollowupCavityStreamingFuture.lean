module
public import QuantitativeFollowup.FollowupCavityFutureMarks
public import QuantitativeFollowup.FollowupCavityStreamingCurrent

@[expose] public section

/-! Exact assembly of the strict-future overlap term against the actual
root-removed Stieltjes measure, including repeated levels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem cavityVertexFutureOverlap_integral (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T))
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    (∑l : Fin n,∫q : Paper.Overlap,if anisotropicVertexOverlap s v<q then
      anisotropicVertexFutureSquare D s v (anisotropicCouplingFeature (cavityIncidentEdge l)) r q else 0
      ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)/(n:ℝ)-
      (∫q : Paper.Overlap,if anisotropicVertexOverlap s v<q then
        (q:ℝ)*anisotropicVertexFutureSquare D s v (cavityCoordinateFeature (Fin.last n)) r q else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)=
      ∫q : Paper.Overlap,if anisotropicVertexOverlap s v<q then cavityFutureVertexConditionalDefect D s v q r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
  have hi (F : Paper.Overlap→ℝ) : Integrable F (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a) := by
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq]
    exact integrable_vectorProfileFreeMeasure s a F
  have he (q : Paper.Overlap) :
      (if anisotropicVertexOverlap s v<q then cavityFutureVertexConditionalDefect D s v q r else 0)=
        (∑l : Fin n,if anisotropicVertexOverlap s v<q then
          anisotropicVertexFutureSquare D s v (anisotropicCouplingFeature (cavityIncidentEdge l)) r q else 0)/(n:ℝ)-
          (if anisotropicVertexOverlap s v<q then
            (q:ℝ)*anisotropicVertexFutureSquare D s v (cavityCoordinateFeature (Fin.last n)) r q else 0) := by
    by_cases h:anisotropicVertexOverlap s v<q
    · simp only [ite_eq_left h,cavityFutureVertexConditionalDefect]
    · simp only [ite_eq_right h,Finset.sum_const_zero,zero_div,sub_zero]
  simp_rw [he]
  rw [integral_sub (hi _) (hi _),integral_div,integral_finset_sum _ (fun _ _=>hi _)]

def cavityRecordedFutureOverlapDefect (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>
    c.1*(∫q : Paper.Overlap,if anisotropicVertexOverlap s c.2<q then
      cavityFutureVertexConditionalDefect (anisotropicReplaceVariance D (Fin.last n) b) s c.2 q r else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))).sum

theorem cavityRecordedFuture_eq_overlapDefect (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    (∑l : Fin n,cavityRecordedIncidentFuture n D s a T b l r)/(n:ℝ)-
      cavityRecordedPathFuture n D s a T b r=cavityRecordedFutureOverlapDefect D s a T b r := by
  classical
  unfold cavityRecordedIncidentFuture cavityRecordedPathFuture cavityRecordedFutureOverlapDefect
  rw [finset_sum_list_map_comm]
  have he (w : ℝ) (f : Fin n→ℝ) : (∑l : Fin n,w*f l)=w*(∑l : Fin n,f l) := (Finset.mul_sum ..).symm
  simp_rw [he]
  rw [←list_sum_map_div_real,←list_sum_map_sub_real]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _
  have hv:=cavityVertexFutureOverlap_integral (anisotropicReplaceVariance D (Fin.last n) b)
    s a ha has hq c.2 r
  have hm : (fun q : Paper.Overlap=>if cavityPathVertexOverlap s c.2<q then
      (q:ℝ)*cavityPathRecordFutureSquare D s (Fin.last n) (trimRoot T) b c.2 r q else 0)=
      fun q : Paper.Overlap=>if anisotropicVertexOverlap s c.2<q then
        (q:ℝ)*anisotropicVertexFutureSquare (anisotropicReplaceVariance D (Fin.last n) b) s c.2
          (cavityCoordinateFeature (Fin.last n)) r q else 0 := rfl
  rw [hm,←hv]
  ring

theorem cavityRecordedStreamingDefect_five_terms (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (ha : 0≤a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    cavityRecordedStreamingDefect n D s a T b r=
      cavityRecordedOriginalOriginalDefect D s T b r-2*cavityRecordedOriginalVertexDefect D s a T b r+
        cavityRecordedVertexVertexDefect D s a T b r+cavityRecordedCurrentOverlapDefect D s a T b r+
          cavityRecordedFutureOverlapDefect D s a T b r := by
  unfold cavityRecordedStreamingDefect
  rw [cavityRecordedStreamingGram_three_terms D s a hq T b r,
    cavityRecordedCurrent_eq_overlapDefect D s a T b r,
    cavityRecordedFuture_eq_overlapDefect D s a ha has hq T b r]

end QuantitativeFollowup
