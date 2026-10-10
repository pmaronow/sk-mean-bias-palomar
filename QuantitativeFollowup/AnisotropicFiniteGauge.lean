module
public import QuantitativeFollowup.AnisotropicSpinPosterior
public import QuantitativePaper.VectorGauge
public import QuantitativePaper.VectorSharpMassBounds

@[expose] public section

/-! Actual spin gauges of arbitrary independent Gaussian coupling scales
and positive diagonal auxiliary covariance. The literal Gaussian recursion
is conjugated, rather than replacing its law by an invariance assumption. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000

def anisotropicParameterGaugeSign (η : Configuration n) : AnisotropicParameterIndex n→ℝ
  | .inl e => Paper.spinSign (η e.1.1)*Paper.spinSign (η e.1.2)
  | .inr i => Paper.spinSign (η i)

theorem abs_anisotropicParameterGaugeSign (η : Configuration n) (i : AnisotropicParameterIndex n) :
    |anisotropicParameterGaugeSign η i|=1 := by
  cases i with
  | inl e => simp only [anisotropicParameterGaugeSign,abs_mul,Paper.abs_spinSign,mul_one]
  | inr i => exact Paper.abs_spinSign _

def anisotropicParameterGauge (η : Configuration n) : AnisotropicParameter n→L[ℝ]AnisotropicParameter n :=
  coordinateSignCLM (anisotropicParameterGaugeSign η) (abs_anisotropicParameterGaugeSign η)

@[simp] theorem anisotropicParameterGauge_apply (η : Configuration n) (P : AnisotropicParameter n)
    (i : AnisotropicParameterIndex n) :
    anisotropicParameterGauge η P i=anisotropicParameterGaugeSign η i*P i := rfl

theorem anisotropicTerminalLinear_gauge (D : AnisotropicSpinModel n) (η σ : Configuration n)
    (P : AnisotropicParameter n) : anisotropicTerminalLinear D σ (anisotropicParameterGauge η P)=
      anisotropicTerminalLinear D (spinGauge η σ) P := by
  unfold anisotropicTerminalLinear
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,spinSign_spinGauge]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    change D.coupling i*Paper.spinSign (σ i.1.1)*Paper.spinSign (σ i.1.2)*
      (anisotropicParameterGauge η P (.inl i)) =
      D.coupling i*(Paper.spinSign (η i.1.1)*Paper.spinSign (σ i.1.1))*
        (Paper.spinSign (η i.1.2)*Paper.spinSign (σ i.1.2))*P (.inl i)
    simp only [anisotropicParameterGauge_apply,anisotropicParameterGaugeSign]
    ring
  · apply Finset.sum_congr rfl
    intro i _
    change Paper.spinSign (σ i)*(anisotropicParameterGauge η P (.inr i)) =
      (Paper.spinSign (η i)*Paper.spinSign (σ i))*P (.inr i)
    simp only [anisotropicParameterGauge_apply,anisotropicParameterGaugeSign]
    ring

theorem anisotropicNoiseMap_gauge (D : AnisotropicSpinModel n) (η : Configuration n) (z : Field n) :
    anisotropicNoiseMap D (fieldGauge η z)=fieldGauge η (anisotropicNoiseMap D z) := by
  ext i
  simp only [anisotropicNoiseMap_apply,fieldGauge_apply]
  ring

theorem anisotropicFieldInjection_gauge (η : Configuration n) (x : Field n) :
    anisotropicParameterGauge η (anisotropicFieldInjection n x)=anisotropicFieldInjection n (fieldGauge η x) := by
  ext i
  cases i <;> simp [anisotropicFieldInjection,anisotropicParameterGauge_apply,anisotropicParameterGaugeSign,fieldGauge_apply]

theorem anisotropicSchemeInput_gauge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (η : Configuration n) (j : ℕ) (z : Field n) :
    anisotropicSchemeInput D s j (fieldGauge η z)=anisotropicParameterGauge η (anisotropicSchemeInput D s j z) := by
  rw [anisotropicSchemeInput_apply,anisotropicSchemeInput_apply,anisotropicNoiseMap_gauge,
    anisotropicFieldInjection_gauge]
  simp only [map_smul]

theorem integral_anisotropicFieldGauge (η : Configuration n) (f : Field n→ℝ) :
    (∫z,f (fieldGauge η z) ∂stdGaussian (Field n))=∫z,f z ∂stdGaussian (Field n) := by
  simpa only [fieldGaussian_eq_stdGaussian] using integral_fieldGauge η f

theorem anisotropicFinitePotential_gauge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (η : Configuration n) (j : ℕ) (P : AnisotropicParameter n) :
    anisotropicFinitePotential D s j (anisotropicParameterGauge η P)=anisotropicFinitePotential D s j P := by
  induction j generalizing P with
  | zero =>
    unfold anisotropicFinitePotential finiteStateGaussianTerminalCascade finiteStateGaussianCascade
      SpinGlass.AT.gtStateLogPartition SpinGlass.AT.gtStatePartition
    simp only [anisotropicEnergyMap_apply,add_zero,anisotropicTerminalLinear_gauge]
    congr 1
    exact (spinGaugeEquiv η).sum_comp (fun σ => Real.exp (anisotropicTerminalLinear D σ P))
  | succ j ih =>
    rw [anisotropicFinitePotential_coleHopf,anisotropicFinitePotential_coleHopf]
    have he (z : Field n) : anisotropicFinitePotential D s j
        (anisotropicParameterGauge η P+anisotropicSchemeInput D s j (fieldGauge η z)) =
        anisotropicFinitePotential D s j (P+anisotropicSchemeInput D s j z) := by
      rw [anisotropicSchemeInput_gauge,←map_add,ih]
    unfold OverlapPaper.sourceLogAverage
    have hi := integral_anisotropicFieldGauge η (fun z => anisotropicFinitePotential D s j
      (anisotropicParameterGauge η P+anisotropicSchemeInput D s j z))
    have hx := integral_anisotropicFieldGauge η (fun z => Real.exp (anisotropicSchemeMass s j*
      anisotropicFinitePotential D s j (anisotropicParameterGauge η P+anisotropicSchemeInput D s j z)))
    simp_rw [he] at hi hx
    split_ifs
    · exact hi.symm
    · rw [←hx]

def anisotropicGaussianGaugeSign (η : Configuration n) : AnisotropicGaussianIndex n k→ℝ
  | .inl e => Paper.spinSign (η e.1.1)*Paper.spinSign (η e.1.2)
  | .inr (_,i) => Paper.spinSign (η i)

theorem abs_anisotropicGaussianGaugeSign (η : Configuration n) (i : AnisotropicGaussianIndex n k) :
    |anisotropicGaussianGaugeSign η i|=1 := by
  cases i with
  | inl e => simp only [anisotropicGaussianGaugeSign,abs_mul,Paper.abs_spinSign,mul_one]
  | inr i => exact Paper.abs_spinSign _

def anisotropicGaussianGaugeEquiv (η : Configuration n) :
    AnisotropicGaussianSpace n k≃ₗᵢ[ℝ]AnisotropicGaussianSpace n k :=
  coordinateSignEquiv (anisotropicGaussianGaugeSign η) (abs_anisotropicGaussianGaugeSign η)

def anisotropicGaussianGauge (η : Configuration n) :
    AnisotropicGaussianSpace n k→L[ℝ]AnisotropicGaussianSpace n k :=
  coordinateSignCLM (anisotropicGaussianGaugeSign η) (abs_anisotropicGaussianGaugeSign η)

@[simp] theorem anisotropicGaussianGauge_apply (η : Configuration n) (z : AnisotropicGaussianSpace n k)
    (i : AnisotropicGaussianIndex n k) :
    anisotropicGaussianGauge η z i=anisotropicGaussianGaugeSign η i*z i := rfl

theorem anisotropicGaussianGauge_gaussian_preserving (η : Configuration n) :
    MeasurePreserving (anisotropicGaussianGauge (k := k) η)
      (stdGaussian (AnisotropicGaussianSpace n k)) (stdGaussian (AnisotropicGaussianSpace n k)) :=
  ⟨(anisotropicGaussianGauge η).continuous.measurable,stdGaussian_map (anisotropicGaussianGaugeEquiv η)⟩

theorem anisotropicEuclideanCoordinates_gauge (η : Configuration n)
    (z : AnisotropicGaussianSpace n k) :
    anisotropicEuclideanCoordinates n k (anisotropicGaussianGauge η z)=
      (WithLp.toLp 2 (fun e => (Paper.spinSign (η e.1.1)*Paper.spinSign (η e.1.2))*
        (anisotropicEuclideanCoordinates n k z).1 e),
        fun j => fieldGauge η ((anisotropicEuclideanCoordinates n k z).2 j)) := by
  apply Prod.ext
  · ext e
    rfl
  · funext j
    ext i
    rfl

theorem anisotropicDisorderInjection_gauge (η : Configuration n) (ω : AnisotropicDisorder n) :
    anisotropicDisorderInjection n (WithLp.toLp 2 (fun e =>
      (Paper.spinSign (η e.1.1)*Paper.spinSign (η e.1.2))*ω e))=
      anisotropicParameterGauge η (anisotropicDisorderInjection n ω) := by
  ext i
  cases i <;> simp [anisotropicDisorderInjection,anisotropicParameterGauge_apply,
    anisotropicParameterGaugeSign]

theorem anisotropicCoordinateUpdate_gauge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (η : Configuration n) (i : ℕ) (P : AnisotropicParameter n) (z : Field n) :
    anisotropicCoordinateUpdate D s i (anisotropicParameterGauge η P) (fieldGauge η z)=
      anisotropicParameterGauge η (anisotropicCoordinateUpdate D s i P z) := by
  simp only [anisotropicCoordinateUpdate,anisotropicSchemeInput_gauge,map_add]

theorem anisotropicEuclideanHistory_gauge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (η : Configuration n) (z : AnisotropicGaussianSpace n k) (i : Fin (k+3)) :
    anisotropicCoordinateHistory D s (anisotropicEuclideanCoordinates n k (anisotropicGaussianGauge η z)) i=
      anisotropicParameterGauge η (anisotropicCoordinateHistory D s (anisotropicEuclideanCoordinates n k z) i) := by
  rw [anisotropicEuclideanCoordinates_gauge]
  unfold anisotropicCoordinateHistory
  rw [anisotropicDisorderInjection_gauge]
  exact independentHistory_covariant _ _ _ (anisotropicCoordinateUpdate_gauge D s η) (k+2)
    (anisotropicDisorderInjection n (anisotropicEuclideanCoordinates n k z).1,
      (anisotropicEuclideanCoordinates n k z).2) i

theorem anisotropicEuclideanStateLinear_gauge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (η : Configuration n) (i : ℕ) (z : AnisotropicGaussianSpace n k) :
    anisotropicEuclideanStateLinear D s i (anisotropicGaussianGauge η z)=
      anisotropicParameterGauge η (anisotropicEuclideanStateLinear D s i z) := by
  simp only [anisotropicEuclideanStateLinear_apply,historyExtended,anisotropicEuclideanHistory_gauge]

theorem anisotropicEuclideanHistoryPotential_gauge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (η : Configuration n) (i : ℕ) (z : AnisotropicGaussianSpace n k) :
    anisotropicEuclideanHistoryPotential D s i (anisotropicGaussianGauge η z)=
      anisotropicEuclideanHistoryPotential D s i z := by
  simp only [anisotropicEuclideanHistoryPotential,anisotropicEuclideanStateLinear_gauge,
    anisotropicFinitePotential_gauge]

theorem anisotropicEuclideanTerminalLinear_gauge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (η σ : Configuration n) (z : AnisotropicGaussianSpace n k) :
    anisotropicEuclideanTerminalLinear D s σ (anisotropicGaussianGauge η z)=
      anisotropicEuclideanTerminalLinear D s (spinGauge η σ) z := by
  simp only [anisotropicEuclideanTerminalLinear,ContinuousLinearMap.comp_apply,
    anisotropicEuclideanStateLinear_gauge,anisotropicTerminalLinear_gauge]

theorem anisotropicPosteriorPotential_gauge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (η σ : Configuration n) (a : ℝ) (z : AnisotropicGaussianSpace n k) :
    anisotropicPosteriorPotential D s a σ (anisotropicGaussianGauge η z)=
      anisotropicPosteriorPotential D s a (spinGauge η σ) z := by
  have hn : ‖anisotropicGaussianGauge η z‖=‖z‖ := (anisotropicGaussianGaugeEquiv η).norm_map z
  simp only [anisotropicPosteriorPotential,standardGaussianPotential,hn,
    anisotropicEuclideanHistoryPotential_gauge,anisotropicEuclideanTerminalLinear_gauge]

theorem anisotropicGaussianGauge_volume_preserving (η : Configuration n) :
    MeasurePreserving (anisotropicGaussianGauge (k := k) η)
      (volume : Measure (AnisotropicGaussianSpace n k)) volume :=
  (anisotropicGaussianGaugeEquiv η).measurePreserving

theorem anisotropicSpinPosteriorMass_gauge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (η σ : Configuration n) (a : ℝ) :
    anisotropicSpinPosteriorMass D s a (spinGauge η σ)=anisotropicSpinPosteriorMass D s a σ := by
  unfold anisotropicSpinPosteriorMass posteriorNormalizer
  rw [←(anisotropicGaussianGauge_volume_preserving (k := k) η).integral_comp
    (anisotropicGaussianGaugeEquiv η).toHomeomorph.measurableEmbedding
    (fun z => Real.exp (-anisotropicPosteriorPotential D s a σ z))]
  simp_rw [anisotropicPosteriorPotential_gauge]

theorem anisotropicSpinPosteriorLaw_gauge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (η σ : Configuration n) (a : ℝ) :
    (anisotropicSpinPosteriorLaw D s a (spinGauge η σ)).map (anisotropicGaussianGauge η)=
      anisotropicSpinPosteriorLaw D s a σ := by
  have hp := anisotropicGaussianGauge_volume_preserving (k := k) η
  let W := fun z => ENNReal.ofReal (Real.exp
    (-normalizedPosteriorPotential (anisotropicPosteriorPotential D s a σ) z))
  have hw : Measurable W := (Real.continuous_exp.comp
    ((contDiff_anisotropicPosteriorPotential D s a σ).continuous.add continuous_const).neg).measurable.ennreal_ofReal
  have he : (fun z => W (anisotropicGaussianGauge η z)) = fun z => ENNReal.ofReal (Real.exp
    (-normalizedPosteriorPotential (anisotropicPosteriorPotential D s a (spinGauge η σ)) z)) := by
    funext z
    unfold W normalizedPosteriorPotential
    rw [anisotropicPosteriorPotential_gauge]
    change ENNReal.ofReal (Real.exp (-(anisotropicPosteriorPotential D s a (spinGauge η σ) z+
      Real.log (anisotropicSpinPosteriorMass D s a σ))))=_
    rw [←anisotropicSpinPosteriorMass_gauge D s η σ a]
    rfl
  have hm := map_withDensity_pullback (volume : Measure (AnisotropicGaussianSpace n k))
    (anisotropicGaussianGauge η) (anisotropicGaussianGauge η).measurable W hw
  rw [hp.map_eq,he] at hm
  exact hm

theorem anisotropicSpinPosterior_integral_gauge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (η σ : Configuration n) (a : ℝ) (f : AnisotropicGaussianSpace n k→ℝ) :
    (∫z,f (anisotropicGaussianGauge η z) ∂anisotropicSpinPosteriorLaw D s a (spinGauge η σ))=
      ∫z,f z ∂anisotropicSpinPosteriorLaw D s a σ := by
  have he : MeasurableEmbedding (anisotropicGaussianGauge (k := k) η) :=
    (anisotropicGaussianGaugeEquiv η).toHomeomorph.measurableEmbedding
  rw [←he.integral_map f,anisotropicSpinPosteriorLaw_gauge]

theorem anisotropicSpinPosterior_invariant_means (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (f : Configuration n→AnisotropicGaussianSpace n k→ℝ)
    (hf : ∀η σ z,f σ (anisotropicGaussianGauge η z)=f (spinGauge η σ) z)
    (σ τ : Configuration n) :
    (∫z,f σ z ∂anisotropicSpinPosteriorLaw D s a σ)=
      ∫z,f τ z ∂anisotropicSpinPosteriorLaw D s a τ := by
  rw [←anisotropicSpinPosterior_integral_gauge D s (spinGauge σ τ) σ a (f σ)]
  simp_rw [hf,spinGauge_connect]

end QuantitativeFollowup
