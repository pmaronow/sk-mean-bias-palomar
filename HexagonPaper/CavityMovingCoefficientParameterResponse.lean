module
public import HexagonPaper.CavityMovingCoefficientMagnetizationVariance
public import HexagonPaper.CavityMovingCoefficientMoments
public import QuantitativeFollowup.AnisotropicVarianceDerivative
public import QuantitativeFollowup.AnisotropicPosteriorLemma

@[expose] public section

/-! Actual coefficient responses at every full disorder/field parameter.
The observable responses are differentiated from the literal native moments. -/
noncomputable section
open Set Filter MeasureTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology BigOperators
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

def cavityMovingParameterDisorder (P : AnisotropicParameter n) : AnisotropicDisorder n :=
  WithLp.toLp 2 (fun e=>P (Sum.inl e))
def cavityMovingParameterField (P : AnisotropicParameter n) : QuantitativePaper.Field n :=
  WithLp.toLp 2 (fun i=>P (Sum.inr i))

theorem cavityMovingParameterDisorder_continuous :
    Continuous (cavityMovingParameterDisorder : AnisotropicParameter n→AnisotropicDisorder n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : AnisotropicCouplingIndex n=>ℝ)).comp
  apply continuous_pi
  intro e
  exact (EuclideanSpace.proj (Sum.inl e)).continuous

theorem cavityMovingParameterField_continuous :
    Continuous (cavityMovingParameterField : AnisotropicParameter n→QuantitativePaper.Field n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n=>ℝ)).comp
  apply continuous_pi
  intro i
  exact (EuclideanSpace.proj (Sum.inr i)).continuous

theorem cavityMovingParameter_split (P : AnisotropicParameter n) :
    anisotropicDisorderInjection n (cavityMovingParameterDisorder P)+
      anisotropicFieldInjection n (cavityMovingParameterField P)=P := by
  ext k
  cases k <;> simp [anisotropicDisorderInjection,anisotropicFieldInjection,
    cavityMovingParameterDisorder,cavityMovingParameterField]

def cavityMovingNativePotentialVarianceDerivative (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i : Fin n) (q : Paper.Overlap) (P : AnisotropicParameter n) : ℝ :=
  anisotropicRestartVarianceResponse D μ (cavityMovingParameterDisorder P) q
    (cavityMovingParameterField P) i

theorem cavityMovingNativePotential_hasDerivAt_variance
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (b : ℝ) (hb : 0<b) :
    HasDerivAt (fun u=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i u) μ q P)
      (cavityMovingNativePotentialVarianceDerivative (anisotropicReplaceVariance D i b) μ i q P) b := by
  have h:=hasDerivAt_anisotropicMeasureTailPotential_variance_restart D μ i
    (cavityMovingParameterDisorder P) q (cavityMovingParameterField P) b hb
  simpa only [cavityMovingParameter_split,cavityMovingNativePotentialVarianceDerivative] using h

theorem cavityMovingNativePotentialVarianceDerivative_joint_continuous
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n) (q : Paper.Overlap) :
    Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter n=>
      cavityMovingNativePotentialVarianceDerivative (anisotropicReplaceVariance D i z.1.val) μ i q z.2) := by
  have harg : Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter n=>
      ((z.1,cavityMovingParameterDisorder z.2),cavityMovingParameterField z.2)) :=
    (continuous_fst.prodMk (cavityMovingParameterDisorder_continuous.comp continuous_snd)).prodMk
      (cavityMovingParameterField_continuous.comp continuous_snd)
  have h:=(cavityNativeVarianceResponse_coefficient_disorder_field_joint_continuous D μ i q).comp harg
  dsimp only [Function.comp_def,cavityMovingNativePotentialVarianceDerivative]
  exact h

def cavityMovingNativeCoordinateVarianceDerivative (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (i j : Fin n) (q : Paper.Overlap) (P : AnisotropicParameter n) : ℝ :=
  cavityNativeTailMagnetizationVarianceDerivative (anisotropicUnitCouplings D) μ i
    (cavityMovingParameterDisorder P) q (cavityMovingParameterField P) j

theorem cavityMovingNativeCoordinate_hasDerivAt_variance
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i j : Fin n)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (b : ℝ) (hb : 0<b) :
    HasDerivAt (fun u=>fderiv ℝ (anisotropicMeasureTailPotential
      (anisotropicUnitCouplings (anisotropicReplaceVariance D i u)) μ q) P
      (anisotropicCoordinateDirection n j))
      (cavityMovingNativeCoordinateVarianceDerivative (anisotropicReplaceVariance D i b) μ i j q P) b := by
  have h:=cavityNativeTailMagnetization_component_hasDerivAt_variance (anisotropicUnitCouplings D) μ i j
    (cavityMovingParameterDisorder P) q (cavityMovingParameterField P) b hb
  simp only [cavityMovingParameter_split,anisotropicMeasureTailMagnetization_apply] at h
  change HasDerivAt (fun u=>fderiv ℝ (anisotropicMeasureTailPotential
    (anisotropicReplaceVariance (anisotropicUnitCouplings D) i u) μ q) P (anisotropicCoordinateDirection n j))
    (cavityNativeTailMagnetizationVarianceDerivative
      (anisotropicReplaceVariance (anisotropicUnitCouplings D) i b) μ i
      (cavityMovingParameterDisorder P) q (cavityMovingParameterField P) j) b
  exact h

theorem cavityMovingNativeCoordinateVarianceDerivative_joint_continuous
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i j : Fin n) (q : Paper.Overlap) :
    Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter n=>
      cavityMovingNativeCoordinateVarianceDerivative (anisotropicReplaceVariance D i z.1.val) μ i j q z.2) := by
  have h:=(cavityNativeTailMagnetizationVarianceDerivative_joint_continuous
    (anisotropicUnitCouplings D) μ i q).comp
    (show Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter n=>
      ((z.1,cavityMovingParameterDisorder z.2),cavityMovingParameterField z.2)) from
      (continuous_fst.prodMk (cavityMovingParameterDisorder_continuous.comp continuous_snd)).prodMk
        (cavityMovingParameterField_continuous.comp continuous_snd))
  have hc:=(EuclideanSpace.proj j).continuous.comp h
  dsimp only [Function.comp_def,cavityMovingNativeCoordinateVarianceDerivative]
  exact hc

def cavityMovingCoefficientMomentVarianceDerivative (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (i : Fin (n+1)) (p : Paper.Overlap)
    (kind : CavityMovingCoefficientMomentKind) (P : AnisotropicParameter (n+1)) : ℝ :=
  let dl:=2*fderiv ℝ (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ p) P
    (anisotropicCoordinateDirection (n+1) (Fin.last n))*
    cavityMovingNativeCoordinateVarianceDerivative D μ i (Fin.last n) p P
  let dr:=(n : ℝ)⁻¹*∑j : Fin n,
    2*fderiv ℝ (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ p) P
      (anisotropicCoordinateDirection (n+1) j.castSucc)*
      cavityMovingNativeCoordinateVarianceDerivative D μ i j.castSucc p P
  match kind with
  | .normalizer=>0
  | .lastSquare=>dl
  | .restSquare=>dr
  | .product=>dl*cavityMovingCoefficientMoment D μ p .restSquare P+
      cavityMovingCoefficientMoment D μ p .lastSquare P*dr

theorem cavityMovingCoefficientMoment_hasDerivAt_variance
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (i : Fin (n+1))
    (p : Paper.Overlap) (kind : CavityMovingCoefficientMomentKind)
    (P : AnisotropicParameter (n+1)) (b : ℝ) (hb : 0<b) :
    HasDerivAt (fun u=>cavityMovingCoefficientMoment (anisotropicReplaceVariance D i u) μ p kind P)
      (cavityMovingCoefficientMomentVarianceDerivative (anisotropicReplaceVariance D i b) μ i p kind P) b := by
  have hc (j : Fin (n+1)):=cavityMovingNativeCoordinate_hasDerivAt_variance D μ i j p P b hb
  have hl : HasDerivAt (fun u=>cavityMovingCoefficientMoment (anisotropicReplaceVariance D i u) μ p .lastSquare P)
      (cavityMovingCoefficientMomentVarianceDerivative (anisotropicReplaceVariance D i b) μ i p .lastSquare P) b := by
    convert (hc (Fin.last n)).pow 2 using 1
    all_goals first | rfl | simp only [cavityMovingCoefficientMoment,cavityFixedRowNativeLastFieldSquare,
      cavityMovingCoefficientMomentVarianceDerivative,pow_one,Nat.cast_ofNat,Nat.reduceSub,
      Pi.pow_apply,Finset.sum_apply]
  have hr : HasDerivAt (fun u=>cavityMovingCoefficientMoment (anisotropicReplaceVariance D i u) μ p .restSquare P)
      (cavityMovingCoefficientMomentVarianceDerivative (anisotropicReplaceVariance D i b) μ i p .restSquare P) b := by
    simpa only [cavityMovingCoefficientMoment,cavityFixedRowNativeRestFieldSquare,
      cavityMovingCoefficientMomentVarianceDerivative,pow_one,Nat.cast_ofNat,Nat.reduceSub,
      Pi.pow_apply,Finset.sum_apply] using
      (HasDerivAt.sum fun j (_ : j∈(Finset.univ : Finset (Fin n)))=>(hc j.castSucc).pow 2).const_mul ((n : ℝ)⁻¹)
  cases kind with
  | normalizer=>simpa only [cavityMovingCoefficientMoment,cavityMovingCoefficientMomentVarianceDerivative]
      using (hasDerivAt_const b (1 : ℝ))
  | lastSquare=>exact hl
  | restSquare=>exact hr
  | product=>convert hl.mul hr using 1 <;> rfl

theorem cavityMovingCoefficientMomentVarianceDerivative_joint_continuous
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (i : Fin (n+1))
    (p : Paper.Overlap) (kind : CavityMovingCoefficientMomentKind) :
    Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter (n+1)=>
      cavityMovingCoefficientMomentVarianceDerivative (anisotropicReplaceVariance D i z.1.val) μ i p kind z.2) := by
  have hl : Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter (n+1)=>
      cavityMovingCoefficientMomentVarianceDerivative (anisotropicReplaceVariance D i z.1.val) μ i p .lastSquare z.2) :=
    (continuous_const.mul (continuous_cavityMovingVarianceCoordinate D μ i (Fin.last n) p)).mul
      (cavityMovingNativeCoordinateVarianceDerivative_joint_continuous D μ i (Fin.last n) p)
  have hr : Continuous (fun z : {b : ℝ // 0<b}×AnisotropicParameter (n+1)=>
      cavityMovingCoefficientMomentVarianceDerivative (anisotropicReplaceVariance D i z.1.val) μ i p .restSquare z.2) :=
    continuous_const.mul (continuous_finsetSum Finset.univ fun (j : Fin n) _=>
      (continuous_const.mul (continuous_cavityMovingVarianceCoordinate D μ i j.castSucc p)).mul
        (cavityMovingNativeCoordinateVarianceDerivative_joint_continuous D μ i j.castSucc p))
  cases kind with
  | normalizer=>exact continuous_const
  | lastSquare=>exact hl
  | restSquare=>exact hr
  | product=>
    exact (hl.mul (continuous_cavityMovingCoefficientMoment_variance D μ i p .restSquare)).add
      ((continuous_cavityMovingCoefficientMoment_variance D μ i p .lastSquare).mul hr)

end HexagonPaper
