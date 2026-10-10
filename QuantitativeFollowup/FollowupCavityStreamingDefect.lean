module
public import QuantitativeFollowup.FollowupCavityPhysicalStreaming
public import QuantitativeFollowup.FollowupCavityPathRecordedStieltjes
public import QuantitativeFollowup.FollowupCavityRowStieltjesCurvature

@[expose] public section

/-! The actual physical interpolation score in overlap-defect form.
The constant terminal charges cancel exactly between the incident row and
last-field path. Right CDF and strict-future Stieltjes terms are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def cavityRecordedIncidentScore (n : ℕ) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ) (l : Fin n)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ:=
  finiteCascadeTreeTerminalFeature (anisotropicCouplingFeature (cavityIncidentEdge l)) (trimRoot T) r.2-
    ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>c.1*
      anisotropicVertexMean (anisotropicReplaceVariance D (Fin.last n) b) s c.2
        (anisotropicCouplingFeature (cavityIncidentEdge l)) r)).sum

def cavityRecordedIncidentCurrent (n : ℕ) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ) (l : Fin n)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ:=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>
    c.1*(Paper.parisiCDF (Paper.parisiSchemeMeasure s) (anisotropicVertexOverlap s c.2)*
      (anisotropicVertexMean (anisotropicReplaceVariance D (Fin.last n) b) s c.2
        (anisotropicCouplingFeature (cavityIncidentEdge l)) r)^2))).sum

def cavityRecordedIncidentFuture (n : ℕ) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ) (l : Fin n)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ:=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>
    c.1*(∫q,if anisotropicVertexOverlap s c.2<q then
      anisotropicVertexFutureSquare (anisotropicReplaceVariance D (Fin.last n) b) s c.2
        (anisotropicCouplingFeature (cavityIncidentEdge l)) r q else 0
          ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))).sum

def cavityRecordedPathCurrent (n : ℕ) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ:=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>
    c.1*(s.q (k+2-c.2.depth)*Paper.parisiCDF (Paper.parisiSchemeMeasure s) (cavityPathVertexOverlap s c.2)*
      (cavityPathRecordMean D s (Fin.last n) (trimRoot T) b c.2 r)^2))).sum

def cavityRecordedPathFuture (n : ℕ) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ:=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map (fun c=>
    c.1*(∫q,if cavityPathVertexOverlap s c.2<q then
      (q:ℝ)*cavityPathRecordFutureSquare D s (Fin.last n) (trimRoot T) b c.2 r q else 0
        ∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a))).sum

def cavityRecordedStreamingDefect (n : ℕ) (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ:=
  (∑l : Fin n,(cavityRecordedIncidentScore n D s a T b l r)^2)/(n:ℝ)-
    cavityPathRecordClockGram D s a (Fin.last n) (trimRoot T) b r+
    ((∑l : Fin n,cavityRecordedIncidentCurrent n D s a T b l r)/(n:ℝ)-
      cavityRecordedPathCurrent n D s a T b r)+
    ((∑l : Fin n,cavityRecordedIncidentFuture n D s a T b l r)/(n:ℝ)-
      cavityRecordedPathFuture n D s a T b r)

theorem cavityPathRecordFeatureCurvature_incident_stieltjes (n : ℕ)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (l : Fin n) (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    cavityPathRecordFeatureCurvature D s a (Fin.last n) (trimRoot T) b (cavityIncidentEdge l) r=
      (cavityRecordedIncidentScore n D s a T b l r)^2-
        (FiniteCascadeGenealogy.leafCount (asGenealogy (trimRoot T)):ℝ)+a+
        cavityRecordedIncidentCurrent n D s a T b l r+cavityRecordedIncidentFuture n D s a T b l r := by
  exact anisotropicIncidentCurvature_free_stieltjes (anisotropicReplaceVariance D (Fin.last n) b)
    s a ha has hq (cavityIncidentEdge l) T r

theorem cavityRecordedCombinedScore_eq_defect (n : ℕ) (hn : 0<n)
    (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    (∑l : Fin n,cavityPathRecordFeatureCurvature D s a (Fin.last n) (trimRoot T) b (cavityIncidentEdge l) r)/(n:ℝ)-
      2*cavityPathRecordScore D s a (Fin.last n) (trimRoot T) b r=
        cavityRecordedStreamingDefect n D s a T b r := by
  have hn0 : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  simp_rw [cavityPathRecordFeatureCurvature_incident_stieltjes n D s a ha has hq T b]
  rw [cavityPathRecordScore_free_stieltjes D s a ha has hq (Fin.last n) (trimRoot T) b r]
  unfold cavityRecordedStreamingDefect cavityRecordedPathCurrent cavityRecordedPathFuture
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  field_simp [hn0]
  <;> ring

theorem followupCavityPhysicalRecordScore_eq_overlap_defect (n : ℕ) (hn : 0<n) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc 0 1) (s : RSBScheme k) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2)) (u : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    followupCavityPhysicalRecordScore n β ρ hβ hρ s a T u r=
      (followupCavityAlpha n β ρ/2)*cavityRecordedStreamingDefect n
        (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩) s a T (followupCavityB n β ρ u) r := by
  classical
  unfold followupCavityPhysicalRecordScore cavityInterpolationRecordScore
  rw [followupCavity_incident_hessian_sum n β ρ hβ hρ]
  rw [←cavityRecordedCombinedScore_eq_defect n hn _ s a ha has hq T _ r]
  ring

end QuantitativeFollowup
