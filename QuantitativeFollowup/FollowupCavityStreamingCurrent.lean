module
public import QuantitativeFollowup.FollowupCavityStreamingPairs
public import QuantitativeFollowup.FollowupCavityOverlapMarks

@[expose] public section

/-! The current right-CDF term is exactly the overlap defect of two
independent terminal continuations from the same retained vertex. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem cavityRecordedMarkPairDefect_vertices (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (b : ℝ) (r : CavityPathRecordSpace (trimRoot T) (n+1))
    (c d : ℝ×FiniteCascadeRecordVertex (trimRoot T)) :
    cavityRecordedMarkPairDefect D s T b r (.inr c) (.inr d)=
      cavityCrossVertexConditionalDefect (anisotropicReplaceVariance D (Fin.last n) b) s c.2 d.2
        (cavityPhysicalCommonOverlap s (trimRoot T) c.2 d.2) r := rfl

def cavityRecordedCurrentOverlapDefect (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>
    c.1*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2)*
      cavityCrossVertexConditionalDefect (anisotropicReplaceVariance D (Fin.last n) b) s c.2 c.2
        (anisotropicVertexOverlap s c.2) r)).sum

theorem cavityRecordedCurrent_eq_overlapDefect (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    (∑l : Fin n,cavityRecordedIncidentCurrent n D s a T b l r)/(n:ℝ)-
      cavityRecordedPathCurrent n D s a T b r=cavityRecordedCurrentOverlapDefect D s a T b r := by
  classical
  unfold cavityRecordedIncidentCurrent cavityRecordedPathCurrent cavityRecordedCurrentOverlapDefect
  rw [finset_sum_list_map_comm]
  rw [←list_sum_map_div_real,←list_sum_map_sub_real]
  apply congrArg List.sum
  apply List.map_congr_left
  intro c _
  have hv : k+2-c.2.depth≤k+2 := by omega
  have hq : (anisotropicVertexOverlap s c.2:ℝ)=s.q (k+2-c.2.depth) :=
    scalarSchemeTransportNode_coe s _ hv
  have he (w m : ℝ) (f : Fin n→ℝ) : (∑l : Fin n,w*(m*(f l)^2))=w*m*(∑l : Fin n,(f l)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  have hm : cavityPathRecordMean D s (Fin.last n) (trimRoot T) b c.2 r=
      anisotropicVertexMean (anisotropicReplaceVariance D (Fin.last n) b) s c.2
        (cavityCoordinateFeature (Fin.last n)) r := rfl
  rw [hm]
  unfold cavityCrossVertexConditionalDefect
  change _=c.1*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2)*_
  simp only [pow_two]
  change _-_ = _
  have hnode : cavityPathVertexOverlap s c.2=anisotropicVertexOverlap s c.2 := rfl
  rw [hnode,hq]
  ring

theorem integral_cavityRecordedCurrent_vertex_overlap
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (v : FiniteCascadeRecordVertex (trimRoot T))
    (F : CavityPathRecordSpace (trimRoot T) (n+1)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hFb : ∀r,|F r|≤C) :
    (∫z,F z.1*cavitySpinOverlapDefect n (anisotropicVertexOverlap s v) z.2.1 z.2.2
      ∂anisotropicCrossVertexMarkedLaw D s a T v v)=
      ∫r,F r*cavityCrossVertexConditionalDefect D s v v (anisotropicVertexOverlap s v) r
        ∂anisotropicTrimmedRecordedTreeLaw D s a T :=
  integral_anisotropicCrossVertexMarkedLaw_overlapDefect D s a T v v _ F hF C hC hFb

end QuantitativeFollowup
