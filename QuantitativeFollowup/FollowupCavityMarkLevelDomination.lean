module
public import FourPapersCommon.FiniteCascadeChargeLevels
public import QuantitativeFollowup.FollowupCavityRootCharges
public import QuantitativeFollowup.ScalarGaussianHistoryCurve

@[expose] public section

/-! Literal free-measure domination of the actual finite cavity level
charges. Branch levels are retained explicitly as inherited marks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency true
variable {k : ℕ}

def cavityProfileLevel (s : RSBScheme k) (j : ℕ) : Paper.Overlap :=
  scalarSchemeTransportNode s (k+2-j)

private theorem scalar_level_sum_range (a χ : ℕ → ℝ) (j : ℕ) :
    finiteCascadeScalarLevelSum a χ j=
      (1-a 0)*χ 0+∑i∈Finset.range j, (a i-a (i+1))*χ (i+1) := by
  induction j with
  | zero => simp [finiteCascadeScalarLevelSum]
  | succ j ih => rw [finiteCascadeScalarLevelSum, ih, Finset.sum_range_succ]; ring

theorem cavityFreeScalarLevelSum_eq_actual_free (s : RSBScheme k) (a : ℝ)
    (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0) (f : Paper.Overlap → ℝ) :
    finiteCascadeFreeScalarLevelSum (anisotropicSchemeMass s)
      (fun j=>f (cavityProfileLevel s j)) (k+1) a=
      ∫q, f q∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
  classical
  have hmass0 : anisotropicSchemeMass s 0=1 := by
    simp only [anisotropicSchemeMass, Nat.sub_zero, s.m_top]
  have hmassK : anisotropicSchemeMass s k=s.m 1 := by
    simp only [anisotropicSchemeMass, show k+1-k=1 by omega]
  have hnode1 : cavityProfileLevel s (k+1)=scalarSchemeTransportNode s 1 := by
    unfold cavityProfileLevel
    congr 1
    omega
  have hatom (i : Fin k) : vectorProfileAtom s (some i)=scalarSchemeTransportNode s (i+2) := by
    apply Subtype.ext
    rw [scalarSchemeTransportNode_coe s (i+2) (by omega)]
    rfl
  have hroot : vectorProfileAtom s none=scalarSchemeTransportNode s 1 := by
    apply Subtype.ext
    rw [scalarSchemeTransportNode_coe s 1 (by omega)]
    rfl
  rw [finiteCascadeFreeScalarLevelSum, scalar_level_sum_range, hmass0, hmassK, hnode1]
  simp only [sub_self, zero_mul, zero_add]
  rw [←Finset.sum_range_reflect (fun j=>(anisotropicSchemeMass s j-anisotropicSchemeMass s (j+1))*
    f (cavityProfileLevel s (j+1))) k]
  have hreflect : (∑j∈Finset.range k,
      (anisotropicSchemeMass s (k-1-j)-anisotropicSchemeMass s (k-1-j+1))*
        f (cavityProfileLevel s (k-1-j+1)))=
      ∑j∈Finset.range k, (s.m (j+2)-s.m (j+1))*f (scalarSchemeTransportNode s (j+2)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjk:=Finset.mem_range.mp hj
    simp only [anisotropicSchemeMass, cavityProfileLevel,
      show k+1-(k-1-j)=j+2 by omega,
      show k+1-(k-1-j+1)=j+1 by omega,
      show k+2-(k-1-j+1)=j+2 by omega]
  rw [hreflect, ←Fin.sum_univ_eq_sum_range]
  rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq,
    integral_vectorProfileFreeMeasure s a has, Fintype.sum_option]
  simp only [vectorPosteriorFeatureWeight, hatom, hroot]
  ring

theorem cavityLevelCharges_le_free_and_branch_marks (s : RSBScheme k) (a : ℝ)
    (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) (f : Paper.Overlap → ℝ) (hf : ∀q, 0 ≤ f q) :
    ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a T).map
      (fun c=>c.1*f (cavityProfileLevel s c.2.depth))).sum ≤ 
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*
        ((∫q, f q∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)+
          finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j)) T) := by
  have hs : a ≤ finiteCascadeStartingMass (anisotropicSchemeMass s) (k+1) := by
    change a ≤ anisotropicSchemeMass s k
    simpa only [anisotropicSchemeMass, show k+1-k=1 by omega] using has
  have hb:=finiteCascadeLevelChargeSum_le_free_and_branches (anisotropicSchemeMass s)
    (fun j=>f (cavityProfileLevel s j)) (anisotropicSchemeMass_antitone s)
    (anisotropicSchemeMass_le_one s 0) (fun _=>hf _) T a hs
  rw [cavityFreeScalarLevelSum_eq_actual_free s a ha has hq f] at hb
  exact hb

end QuantitativeFollowup
