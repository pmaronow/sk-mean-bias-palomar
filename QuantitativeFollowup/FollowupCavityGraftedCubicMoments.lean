module
public import QuantitativeFollowup.FollowupCavityBranchCubic
public import QuantitativeFollowup.FollowupCavityGraftCubicBudget

@[expose] public section

/-! The actual three-defect moments of all charged single-graft trees
obey the free-measure/branch budget. Pair choices name real distinct
terminal descendants; no marginal or moment estimate is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityRecordedTripleDefectMoment (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (i k : Fin 3→ObservationLeaf T) : ℝ :=
  ∫z,|cavitySpinOverlapDefect n (q (observationCommonLevel T (i 0) (k 0)))
    (observationLeafSpin T (i 0) z.2) (observationLeafSpin T (k 0) z.2)*
    cavitySpinOverlapDefect n (q (observationCommonLevel T (i 1) (k 1)))
    (observationLeafSpin T (i 1) z.2) (observationLeafSpin T (k 1) z.2)*
    cavitySpinOverlapDefect n (q (observationCommonLevel T (i 2) (k 2)))
    (observationLeafSpin T (i 2) z.2) (observationLeafSpin T (k 2) z.2)|
    ∂anisotropicRecordedProfileTreeLaw D μ a q T

theorem cavityProfileLevel_clock (s : RSBScheme k) :
    cavityProfileLevel s 0=1 ∧ cavityProfileLevel s (k+2)=0 ∧
      ∀l,l<k+2→cavityProfileLevel s (l+1)≤cavityProfileLevel s l := by
  constructor
  · apply Subtype.ext
    rw [cavityProfileLevel,Nat.sub_zero,scalarSchemeTransportNode_coe s _ le_rfl,s.q_top]
    rfl
  constructor
  · apply Subtype.ext
    rw [cavityProfileLevel,Nat.sub_self,scalarSchemeTransportNode_coe s 0 (by omega),s.q_zero]
    rfl
  intro l hl
  change (cavityProfileLevel s (l+1):ℝ)≤(cavityProfileLevel s l:ℝ)
  rw [cavityProfileLevel,cavityProfileLevel,
    scalarSchemeTransportNode_coe s _ (by omega),scalarSchemeTransportNode_coe s _ (by omega)]
  exact s.q_mono' (k+2-l) (by omega) (k+2-(l+1)) (by omega)

def cavityChargedGraftTripleMoment (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (T : FiniteTerminalGenealogy (k+2))
    (i k : (v : FiniteCascadeRecordVertex (trimRoot T))→
      Fin 3→ObservationLeaf (.advance (finiteCascadeVertexGraft v))) : ℝ :=
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
    (fun c=>c.1*cavityRecordedTripleDefectMoment D (Paper.parisiSchemeMeasure s) a
      (cavityProfileLevel s) (.advance (finiteCascadeVertexGraft c.2)) (i c.2) (k c.2))).sum

theorem cavityChargedGraftTripleMoment_le_free_cubic (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2))
    (i k : (v : FiniteCascadeRecordVertex (trimRoot T))→
      Fin 3→ObservationLeaf (.advance (finiteCascadeVertexGraft v)))
    (hik : ∀v r,i v r≠k v r) :
    cavityChargedGraftTripleMoment D s a T i k≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          2*finiteCascadeUnweightedBranchSum
            (fun l=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s l))
            (trimRoot T)) := by
  obtain ⟨hzero,hroot,hmono⟩:=cavityProfileLevel_clock s
  have hb : cavityChargedGraftTripleMoment D s a T i k≤
      cavityChargedGraftBranchBudget s a T (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a) := by
    unfold cavityChargedGraftTripleMoment cavityChargedGraftBranchBudget
    apply List.sum_le_sum
    intro c hc
    have hh:=cavityRecorded_threeDefects_le_branch_cubic D (Paper.parisiSchemeMeasure s) a
      (cavityProfileLevel s) hzero (.advance (finiteCascadeVertexGraft c.2)) hroot hmono
      (i c.2) (k c.2) (hik c.2)
    exact mul_le_mul_of_nonneg_left hh (anisotropicTrimmedVertexCharges_nonneg s a has T c hc)
  exact hb.trans (cavityChargedGraftBranchBudget_le s a ha has hq T
    (cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a)
    (fun q=>(cavityCubicPairMoment_bounds D (Paper.parisiSchemeMeasure s) a q).1))

end QuantitativeFollowup
