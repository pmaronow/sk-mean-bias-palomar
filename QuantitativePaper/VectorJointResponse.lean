module
public import QuantitativePaper.VectorFieldSliceJetBounds
public import QuantitativePaper.VectorResponseTestData

@[expose] public section

/-! Literal weighted Gaussian responses as jointly smooth functions of
initial disorder and field. The actual vector shift leaves disorder fixed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ}

def vectorJointResponse (F G : VectorParameter n → ℝ) (v m : ℝ) (p : VectorParameter n) : ℝ :=
  vectorStepResponse v m (fun x=>F (p.1,x)) (fun x=>G (p.1,x)) p.2

def vectorJointColeHopf (F : VectorParameter n → ℝ) (v m : ℝ) (p : VectorParameter n) : ℝ :=
  vectorColeHopfStep v m (fun x=>F (p.1,x)) p.2

theorem vectorJointResponse_eq_weightedRatio (F G : VectorParameter n → ℝ) (v m : ℝ) :
    vectorJointResponse F G v m=gaussianWeightedShiftRatio (vectorJointShift n v) m F G := by
  funext p
  unfold vectorJointResponse vectorStepResponse vectorStepWeight vectorStepPartition
    gaussianWeightedShiftRatio gaussianWeightedShiftMoment gaussianShiftPartition
  simp_rw [vectorJointShift_add]
  have he : (fun z=>Real.exp (m*F (p.1,fieldShift v p.2 z))/
      (∫ w,Real.exp (m*F (p.1,fieldShift v p.2 w)) ∂fieldGaussian n)*G (p.1,fieldShift v p.2 z))=
      (fun z=>(Real.exp (m*F (p.1,fieldShift v p.2 z))*G (p.1,fieldShift v p.2 z))/
        (∫ w,Real.exp (m*F (p.1,fieldShift v p.2 w)) ∂fieldGaussian n)) := by
    funext z
    ring
  rw [he,integral_div]

theorem vectorJointColeHopf_eq_gaussianShift (F : VectorParameter n → ℝ) (v m : ℝ) :
    vectorJointColeHopf F v m=gaussianShiftColeHopf (vectorJointShift n v) m F := by
  funext p
  unfold vectorJointColeHopf vectorColeHopfStep vectorStepPartition gaussianShiftColeHopf
    gaussianShiftPartition gaussianShiftAverage
  simp_rw [vectorJointShift_add]

structure VectorJointResponseTestData (F G : VectorParameter n → ℝ) where
  potentialRegularity : ContDiff ℝ 3 F
  observableRegularity : ContDiff ℝ 3 G
  fieldLip : ℝ≥0
  lipschitz : LipschitzWith fieldLip F
  potentialPower : ℝ≥0
  potentialPower_ge_one : 1≤potentialPower
  potentialJets : ∀ j,1≤j → j≤3 → ∀ p,‖iteratedFDeriv ℝ j F p‖≤(potentialPower : ℝ)^j
  observableBounds : ℕ → ℝ
  observableBounds_nonneg : ∀ j,0≤observableBounds j
  observableJets : ∀ j,j≤3 → ∀ p,‖iteratedFDeriv ℝ j G p‖≤observableBounds j

def VectorJointResponseTestData.fieldData {F G : VectorParameter n → ℝ}
    (d : VectorJointResponseTestData F G) (p : Couplings n×ℝ) :
    VectorResponseTestData (fun x=>F (p,x)) (fun x=>G (p,x)) where
  potentialRegularity := d.potentialRegularity.comp (contDiff_const.prodMk contDiff_id)
  observableRegularity := d.observableRegularity.comp (contDiff_const.prodMk contDiff_id)
  fieldLip := d.fieldLip
  lipschitz := lipschitzWith_fieldSlice d.lipschitz p
  potentialPower := d.potentialPower
  potentialPower_ge_one := d.potentialPower_ge_one
  potentialJets := fun j hj hjN x=>norm_iteratedFDeriv_fieldSlice_le F d.potentialRegularity hjN p x
    _ (pow_nonneg d.potentialPower.coe_nonneg _) (d.potentialJets j hj hjN)
  observableBounds := d.observableBounds
  observableBounds_nonneg := d.observableBounds_nonneg
  observableJets := fun j hjN x=>norm_iteratedFDeriv_fieldSlice_le G d.observableRegularity hjN p x
    _ (d.observableBounds_nonneg j) (d.observableJets j hjN)

theorem VectorJointResponseTestData.response_uniform_jets {F G : VectorParameter n → ℝ}
    (d : VectorJointResponseTestData F G) (m : ℝ) :
    ∃ B : ℕ→ℝ,(∀ j,0≤B j) ∧ ∀ v,ContDiff ℝ 3 (vectorJointResponse F G v m) ∧
      ∀ j,j≤3 → ∀ p,‖iteratedFDeriv ℝ j (vectorJointResponse F G v m) p‖≤B j := by
  obtain ⟨B,hB,hjets⟩ := gaussianWeightedShiftRatio_uniform_jets 3 F G
    d.potentialRegularity d.observableRegularity d.fieldLip d.lipschitz m d.potentialPower
    d.potentialPower.coe_nonneg d.observableBounds d.observableBounds_nonneg
    d.potentialJets d.observableJets
  refine ⟨B,hB,fun v=>?_⟩
  rw [vectorJointResponse_eq_weightedRatio]
  exact hjets _

theorem VectorJointResponseTestData.coleHopf_uniform_jets {F G : VectorParameter n → ℝ}
    (d : VectorJointResponseTestData F G) (m : ℝ) :
    (∀ v,ContDiff ℝ 3 (vectorJointColeHopf F v m)) ∧
      ∃ D : ℝ,1≤D ∧ ∀ v j,1≤j → j≤3 → ∀ p,
        ‖iteratedFDeriv ℝ j (vectorJointColeHopf F v m) p‖≤D^j := by
  obtain ⟨D,hD,hB⟩ := gaussianShiftColeHopf_uniform_shift_jets 3 F d.potentialRegularity
    d.fieldLip d.lipschitz d.potentialPower (show 1≤(d.potentialPower : ℝ) from d.potentialPower_ge_one)
    d.potentialJets m
  refine ⟨fun v=>?_,D,hD,fun v j hj hjN p=>?_⟩
  · rw [vectorJointColeHopf_eq_gaussianShift]
    exact (gaussianShiftColeHopf_smooth_bounded_jets 3 F d.potentialRegularity d.fieldLip d.lipschitz
      d.potentialPower (show 1≤(d.potentialPower : ℝ) from d.potentialPower_ge_one)
      d.potentialJets (vectorJointShift n v) m).1
  · rw [vectorJointColeHopf_eq_gaussianShift]
    exact hB (vectorJointShift n v) j hj hjN p

end QuantitativePaper
