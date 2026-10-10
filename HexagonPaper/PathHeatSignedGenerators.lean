module
public import HexagonPaper.PathHeatSignedTensorJet

@[expose] public section

/-! The two bounded uncentered signed generators whose normalized
response is the manuscript's exact centered covariance formula. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]

def pathHeatDensityDerivativeMeasure (S : SignedMeasure X) (M : SignedMeasure (X×X)) :
    SignedMeasure (X×X) := M+pathHeatSignedTensor S S

def pathHeatObservableDerivativeMeasure (S P : SignedMeasure X) (Q : SignedMeasure (X×X)) :
    SignedMeasure (X×X) := Q+pathHeatSignedTensor S P+pathHeatSignedTensor P S

def pathHeatDensityGenerator (K : X×X→ᵇℝ) (S : SignedMeasure X)
    (M : SignedMeasure (X×X)) (dotell : ℝ) : ℝ :=
  dotell+(1/2:ℝ)*signedContraction K (pathHeatDensityDerivativeMeasure S M)

def pathHeatObservableGenerator (K : X×X→ᵇℝ) (S P : SignedMeasure X)
    (Q : SignedMeasure (X×X)) (dotphi : ℝ) : ℝ :=
  dotphi+(1/2:ℝ)*signedContraction K (pathHeatObservableDerivativeMeasure S P Q)

theorem signedContraction_add (K : X×X→ᵇℝ) (M Q : SignedMeasure (X×X)) :
    signedContraction K (M+Q)=signedContraction K M+signedContraction K Q := by
  exact VectorMeasure.integral_add_vectorMeasure (K.integrable M.variation) (K.integrable Q.variation)

theorem signedContraction_smul (K : X×X→ᵇℝ) (c : ℝ) (M : SignedMeasure (X×X)) :
    signedContraction K (c•M)=c*signedContraction K M :=
  VectorMeasure.integral_smul_vectorMeasure K c

theorem pathHeat_generators_centered_identity (K : X×X→ᵇℝ) (S P : SignedMeasure X)
    (M Q : SignedMeasure (X×X)) (dotell dotphi phi center : ℝ) :
    pathHeatObservableGenerator K S P Q dotphi+(phi-center)*pathHeatDensityGenerator K S M dotell=
      dotphi+(phi-center)*dotell+(1/2:ℝ)*signedContraction K
        (pathHeatCenteredDerivativeMeasure S P M Q phi center) := by
  simp only [pathHeatDensityGenerator,pathHeatObservableGenerator,
    pathHeatDensityDerivativeMeasure,pathHeatObservableDerivativeMeasure,
    pathHeatCenteredDerivativeMeasure,signedContraction_add,signedContraction_smul]
  ring

theorem pathHeatDensityGenerator_bound (K : X×X→ᵇℝ) (S : SignedMeasure X)
    (M : SignedMeasure (X×X)) (dotell : ℝ) :
    ‖pathHeatDensityGenerator K S M dotell‖≤
      ‖dotell‖+(1/2:ℝ)*‖K‖*(signedTV M+signedTV S*signedTV S) := by
  have h := norm_signedContraction_le K (pathHeatDensityDerivativeMeasure S M)
  have ht : signedTV (pathHeatDensityDerivativeMeasure S M)≤signedTV M+signedTV S*signedTV S :=
    (signedTV_add_le _ _).trans (add_le_add le_rfl (signedTV_pathHeatSignedTensor_le _ _))
  unfold pathHeatDensityGenerator
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  rw [norm_mul,show ‖(1/2:ℝ)‖=1/2 from by norm_num]
  exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans
    (by nlinarith [mul_le_mul_of_nonneg_left ht (norm_nonneg K)])

theorem pathHeatObservableGenerator_bound (K : X×X→ᵇℝ) (S P : SignedMeasure X)
    (Q : SignedMeasure (X×X)) (dotphi : ℝ) :
    ‖pathHeatObservableGenerator K S P Q dotphi‖≤
      ‖dotphi‖+(1/2:ℝ)*‖K‖*(signedTV Q+2*signedTV S*signedTV P) := by
  have h := norm_signedContraction_le K (pathHeatObservableDerivativeMeasure S P Q)
  have ht : signedTV (pathHeatObservableDerivativeMeasure S P Q)≤
      signedTV Q+2*signedTV S*signedTV P := by
    apply (signedTV_add_le _ _).trans
    have hq := (signedTV_add_le Q (pathHeatSignedTensor S P)).trans
      (add_le_add le_rfl (signedTV_pathHeatSignedTensor_le S P))
    have hp := signedTV_pathHeatSignedTensor_le P S
    linarith
  unfold pathHeatObservableGenerator
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  rw [norm_mul,show ‖(1/2:ℝ)‖=1/2 from by norm_num]
  exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans
    (by nlinarith [mul_le_mul_of_nonneg_left ht (norm_nonneg K)])

end HexagonPaper
