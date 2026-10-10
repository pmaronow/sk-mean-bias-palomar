module
public import QuantitativeFollowup.FollowupCavityStreamingDefect
public import FourPapersCommon.ListSignedGram

@[expose] public section

/-! The original-original, original-vertex and vertex-vertex part of the
actual streaming defect, expanded at retained records. -/
noncomputable section
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem cavityPhysicalCommonOverlap_symm (s : RSBScheme k) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v w : FiniteCascadeRecordVertex T) :
    cavityPhysicalCommonOverlap s T v w=cavityPhysicalCommonOverlap s T w v := by
  have hv:=cavityPhysicalPath_covariance_clock s (0:Fin 1) T v w
  have hw:=cavityPhysicalPath_covariance_clock s (0:Fin 1) T w v
  have he : (∑e : GaussianCoordinateIndex (Fin 1) T,
      finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) (0:Fin 1) v e*
        finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) (0:Fin 1) w e)=
      ∑e : GaussianCoordinateIndex (Fin 1) T,
      finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) (0:Fin 1) w e*
        finiteCascadePathCoefficient (cavityPhysicalEdgeCoefficient s) (0:Fin 1) v e := by
    apply Finset.sum_congr rfl
    intro e _
    ring
  linarith only [hv,hw,he]

theorem cavityPhysicalCommonOverlap_self (s : RSBScheme k) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T) :
    cavityPhysicalCommonOverlap s T v v=s.q (k+2-v.depth) := by
  unfold cavityPhysicalCommonOverlap
  rw [finiteCascadeCommonPathDepth_self]

theorem finiteCascadeTreeTerminalFeature_eq_terminal_vertex_sum
    {S : Type} [Fintype S] (K : FiniteStateField S) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (z : Records (FiniteStateField S) S T) :
    finiteCascadeTreeTerminalFeature K T z=
      ((finiteCascadeTerminalVertices T (finiteCascadeRecordTerminalSpins T z)).map
        (fun c=>K c.2)).sum := by
  induction T with
  | leaf => simp [finiteCascadeTreeTerminalFeature,finiteCascadeTerminalVertices,
      finiteCascadeRecordTerminalSpins]
  | advance T ih =>
    simpa only [finiteCascadeTreeTerminalFeature,finiteCascadeTerminalVertices,
      finiteCascadeRecordTerminalSpins,List.map_map,Function.comp_def] using ih z.2
  | fork T U ihT ihU =>
    simp only [finiteCascadeTreeTerminalFeature,finiteCascadeTerminalVertices,
      finiteCascadeRecordTerminalSpins,List.map_append,List.sum_append,List.map_map,Function.comp_def]
    exact congrArg₂ (fun x y : ℝ=>x+y) (ihT z.1) (ihU z.2)

abbrev CavityRecordedStreamingMark (n : ℕ) {j : ℕ} (T : FiniteTerminalGenealogy j) :=
  Sum (FiniteCascadeRecordVertex T×Configuration (n+1)) (ℝ×FiniteCascadeRecordVertex T)

def cavityRecordedMarkVertex {j : ℕ} {T : FiniteTerminalGenealogy j}
    (m : CavityRecordedStreamingMark n T) : FiniteCascadeRecordVertex T :=
  m.elim Prod.fst Prod.snd

def cavityRecordedMarkIncidentMean (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1))
    (m : CavityRecordedStreamingMark n (trimRoot T)) (l : Fin n) : ℝ :=
  m.elim (fun c=>anisotropicCouplingFeature (cavityIncidentEdge l) c.2)
    (fun c=>anisotropicVertexMean (anisotropicReplaceVariance D (Fin.last n) b) s c.2
      (anisotropicCouplingFeature (cavityIncidentEdge l)) r)

def cavityRecordedMarkEpsilonMean (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1))
    (m : CavityRecordedStreamingMark n (trimRoot T)) : ℝ :=
  m.elim (fun c=>Paper.spinSign (c.2 (Fin.last n)))
    (fun c=>cavityPathRecordMean D s (Fin.last n) (trimRoot T) b c.2 r)

def cavityRecordedMarkPairDefect (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1))
    (m m' : CavityRecordedStreamingMark n (trimRoot T)) : ℝ :=
  (∑l : Fin n,cavityRecordedMarkIncidentMean D s T b r m l*
    cavityRecordedMarkIncidentMean D s T b r m' l)/(n:ℝ)-
      cavityPhysicalCommonOverlap s (trimRoot T) (cavityRecordedMarkVertex m) (cavityRecordedMarkVertex m')*
        cavityRecordedMarkEpsilonMean D s T b r m*cavityRecordedMarkEpsilonMean D s T b r m'

theorem cavityRecordedMarkPairDefect_symm (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1))
    (m m' : CavityRecordedStreamingMark n (trimRoot T)) :
    cavityRecordedMarkPairDefect D s T b r m m'=cavityRecordedMarkPairDefect D s T b r m' m := by
  unfold cavityRecordedMarkPairDefect
  rw [cavityPhysicalCommonOverlap_symm s (trimRoot T) (cavityRecordedMarkVertex m) (cavityRecordedMarkVertex m')]
  have he : (∑l : Fin n,cavityRecordedMarkIncidentMean D s T b r m l*
      cavityRecordedMarkIncidentMean D s T b r m' l)=
      ∑l : Fin n,cavityRecordedMarkIncidentMean D s T b r m' l*
        cavityRecordedMarkIncidentMean D s T b r m l := by
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  ring

def cavityRecordedStreamingSignedMarks (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2))
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    List (ℝ×CavityRecordedStreamingMark n (trimRoot T)) :=
  (finiteCascadeTerminalVertices (trimRoot T) (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)).map
    (fun c=>((1:ℝ),Sum.inl c))++
  (finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>(-c.1,Sum.inr c))

theorem cavityRecordedStreamingSignedMarks_incident (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) (l : Fin n) :
    ((cavityRecordedStreamingSignedMarks s a T r).map (fun c=>
      c.1*cavityRecordedMarkIncidentMean D s T b r c.2 l)).sum=
        cavityRecordedIncidentScore n D s a T b l r := by
  unfold cavityRecordedStreamingSignedMarks cavityRecordedMarkIncidentMean cavityRecordedIncidentScore
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,
    Sum.elim_inl,Sum.elim_inr,one_mul,neg_mul,list_sum_map_neg_real]
  rw [←finiteCascadeTreeTerminalFeature_eq_terminal_vertex_sum]
  ring

theorem cavityRecordedStreamingSignedMarks_clock (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    ((cavityRecordedStreamingSignedMarks s a T r).map (fun c=>
      ((cavityRecordedStreamingSignedMarks s a T r).map (fun d=>
        c.1*cavityRecordedMarkEpsilonMean D s T b r c.2*
          (d.1*cavityRecordedMarkEpsilonMean D s T b r d.2)*
          cavityPhysicalCommonOverlap s (trimRoot T) (cavityRecordedMarkVertex c.2)
            (cavityRecordedMarkVertex d.2))).sum)).sum=
      cavityPathRecordClockGram D s a (Fin.last n) (trimRoot T) b r := by
  have hm : ((cavityRecordedStreamingSignedMarks s a T r).map (fun c=>
      (c.1*cavityRecordedMarkEpsilonMean D s T b r c.2,cavityRecordedMarkVertex c.2)))=
      cavityPathRecordSignedMarks D s a (Fin.last n) (trimRoot T) b r := by
    unfold cavityRecordedStreamingSignedMarks cavityRecordedMarkEpsilonMean
      cavityRecordedMarkVertex cavityPathRecordSignedMarks
    simp only [List.map_append,List.map_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr,one_mul]
  unfold cavityPathRecordClockGram
  rw [←hm]
  simp only [List.map_map,Function.comp_def,show k+2-(k+2-1)=1 by omega,hq,sub_zero]

theorem cavityRecordedStreamingGram_eq_pairs (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    (∑l : Fin n,(cavityRecordedIncidentScore n D s a T b l r)^2)/(n:ℝ)-
      cavityPathRecordClockGram D s a (Fin.last n) (trimRoot T) b r=
      ((cavityRecordedStreamingSignedMarks s a T r).map (fun c=>
        ((cavityRecordedStreamingSignedMarks s a T r).map (fun d=>
          c.1*d.1*cavityRecordedMarkPairDefect D s T b r c.2 d.2)).sum)).sum := by
  have hc:=finite_weighted_defect_contraction (cavityRecordedStreamingSignedMarks s a T r)
    (cavityRecordedMarkIncidentMean D s T b r) (cavityRecordedMarkEpsilonMean D s T b r)
    (fun c d=>cavityPhysicalCommonOverlap s (trimRoot T) (cavityRecordedMarkVertex c)
      (cavityRecordedMarkVertex d)) (n:ℝ)
  simp_rw [cavityRecordedStreamingSignedMarks_incident D s a T b r] at hc
  rw [cavityRecordedStreamingSignedMarks_clock D s a hq T b r] at hc
  exact hc

def cavityRecordedOriginalOriginalDefect (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ :=
  let xs:=finiteCascadeTerminalVertices (trimRoot T) (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)
  (xs.map (fun c=>(xs.map (fun d=>cavityRecordedMarkPairDefect D s T b r (.inl c) (.inl d))).sum)).sum

def cavityRecordedOriginalVertexDefect (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ :=
  ((finiteCascadeTerminalVertices (trimRoot T) (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)).map
    (fun c=>((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
      (fun d=>d.1*cavityRecordedMarkPairDefect D s T b r (.inl c) (.inr d))).sum)).sum

def cavityRecordedVertexVertexDefect (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ :=
  let ys:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  (ys.map (fun c=>(ys.map (fun d=>c.1*d.1*cavityRecordedMarkPairDefect D s T b r (.inr c) (.inr d))).sum)).sum

theorem cavityRecordedStreamingGram_three_terms (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    (∑l : Fin n,(cavityRecordedIncidentScore n D s a T b l r)^2)/(n:ℝ)-
      cavityPathRecordClockGram D s a (Fin.last n) (trimRoot T) b r=
        cavityRecordedOriginalOriginalDefect D s T b r-
          2*cavityRecordedOriginalVertexDefect D s a T b r+cavityRecordedVertexVertexDefect D s a T b r := by
  rw [cavityRecordedStreamingGram_eq_pairs D s a hq T b r]
  exact list_signed_gram_expansion
    (finiteCascadeTerminalVertices (trimRoot T) (finiteCascadeRecordTerminalSpins (trimRoot T) r.2))
    (finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)) Prod.fst
    (cavityRecordedMarkPairDefect D s T b r) (cavityRecordedMarkPairDefect_symm D s T b r)

end QuantitativeFollowup
