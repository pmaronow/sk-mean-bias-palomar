module
public import QuantitativeFollowup.FollowupCavityChargedCrossResponseCubic
public import FourPapersCommon.FiniteCascadeVertexGraftLeafGeometry

@[expose] public section

/-! A single old overlap defect multiplied by a genuine cross-graft
mark is an actual two-pair observable of the enlarged genealogy. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityCrossGraftPairLeft {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) (i : ObservationLeaf T) :
    Fin 2→ObservationLeaf (finiteCascadeCrossVertexGraft v w) := fun b=>
  if b=0 then finiteCascadeCrossGraftOldLeaf v w i else finiteCascadeCrossGraftFirstLeaf v w

def cavityCrossGraftPairRight {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) (l : ObservationLeaf T) :
    Fin 2→ObservationLeaf (finiteCascadeCrossVertexGraft v w) := fun b=>
  if b=0 then finiteCascadeCrossGraftOldLeaf v w l else finiteCascadeCrossGraftSecondLeaf v w

theorem cavityRecordedPairProduct_cross_graft (s : RSBScheme k) {j : ℕ}
    {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (i l : ObservationLeaf T) (r : CavityPathRecordSpace (finiteCascadeCrossVertexGraft v w) (n+1)) :
    cavityRecordedPairProduct s (finiteCascadeCrossVertexGraft v w)
      (cavityCrossGraftPairLeft v w i) (cavityCrossGraftPairRight v w l) r=
      cavityRecordedLeafPairDefect s T i l (finiteCascadeCrossGraftExtract v w r.2).1*
        cavitySpinOverlapDefect n (cavityProfileLevel s (finiteCascadeCommonPathDepth T v w))
          (finiteCascadeCrossGraftExtract v w r.2).2.1 (finiteCascadeCrossGraftExtract v w r.2).2.2 := by
  simp only [cavityRecordedPairProduct,cavityCrossGraftPairLeft,cavityCrossGraftPairRight,
    if_pos rfl,ite_true,show (1 : Fin 2)≠0 by decide,ite_false,cavityRecordedLeafPairDefect,
    finiteCascadeCrossGraftOldLeaf_commonLevel,finiteCascadeCrossGraftOldLeaf_spin,
    finiteCascadeCrossGraftFresh_commonLevel,finiteCascadeCrossGraftFirstLeaf_spin,
    finiteCascadeCrossGraftSecondLeaf_spin]

theorem cavityCrossGraftPair_dominated (s : RSBScheme k) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (i l : ObservationLeaf (trimRoot T))
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (spins (trimRoot T) r.2)|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (v w : FiniteCascadeRecordVertex (trimRoot T))
    (r : CavityPathRecordSpace (finiteCascadeCrossVertexGraft v w) (n+1)) :
    |followupCavityPhysicalRecordObservable n (.advance (finiteCascadeCrossVertexGraft v w))
      (cavityCrossGraftSampleObservable T v w (cavityProfileLevel s
        (finiteCascadeCommonPathDepth (trimRoot T) v w)) F) r|≤
      |cavityRecordedPairProduct s (finiteCascadeCrossVertexGraft v w)
        (cavityCrossGraftPairLeft v w i) (cavityCrossGraftPairRight v w l) r| := by
  rw [cavityCrossGraftSampleObservable_record,cavityRecordedPairProduct_cross_graft,abs_mul,abs_mul]
  exact mul_le_mul_of_nonneg_right (hF (r.1,(finiteCascadeCrossGraftExtract v w r.2).1)) (abs_nonneg _)

theorem anisotropicVertexOverlap_eq_cross_self (s : RSBScheme k)
    {T : FiniteTerminalGenealogy (k+2)} (v : FiniteCascadeRecordVertex (trimRoot T)) :
    anisotropicVertexOverlap s v=cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) v v) := by
  apply Subtype.ext
  rw [←cavityPhysicalCommonOverlap_eq_profileLevel,cavityPhysicalCommonOverlap_self]
  exact scalarSchemeTransportNode_coe s (k+2-v.depth) (Nat.sub_le _ _)

theorem followupCavityCrossGraftDerivative_singlePair_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (i l : ObservationLeaf (trimRoot T))
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (spins (trimRoot T) r.2)|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |followupCavityCrossGraftDerivative n β ρ hβ hρ s a T F u hu|≤
      followupCavityAlpha n β ρ/2*(45*(L+2)^2*L^2)*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) :=
  followupCavityCrossGraftDerivative_cubic_le hn β ρ hβ hρ s a ha has hq T F
    (fun v w=>cavityCrossGraftPairLeft v w i) (fun v w=>cavityCrossGraftPairRight v w l)
    (cavityCrossGraftPair_dominated s T F i l hF) u hu

theorem followupCavityCurrentGraftDerivative_singlePair_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy (trimRoot T))→ℝ)
    (i l : ObservationLeaf (trimRoot T))
    (hF : ∀r : CavityPathRecordSpace (trimRoot T) (n+1),
      |F (spins (trimRoot T) r.2)|≤|cavityRecordedLeafPairDefect s (trimRoot T) i l r.2|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    let L : ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
    |followupCavityCurrentGraftDerivative n β ρ hβ hρ s a T F u hu|≤
      followupCavityAlpha n β ρ/2*(45*(L+2)^2*L)*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)) := by
  apply followupCavityCurrentGraftDerivative_cubic_le hn β ρ hβ hρ s a ha has hq T F
    (fun v=>cavityCrossGraftPairLeft v v i) (fun v=>cavityCrossGraftPairRight v v l) _ u hu
  intro v r
  rw [anisotropicVertexOverlap_eq_cross_self]
  exact cavityCrossGraftPair_dominated s T F i l hF v v r

end QuantitativeFollowup
