module
public import QuantitativeFollowup.AnisotropicFiniteGauge
public import QuantitativeFollowup.AnisotropicPosteriorJets
public import QuantitativePaper.VectorMagnetizationGauge

@[expose] public section

/-! The actual anisotropic field response, its bounded smooth coordinates,
and its covariance under Gaussian spin gauges. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000

def anisotropicCoordinateDirection (n : ℕ) (i : Fin n) : AnisotropicParameter n :=
  anisotropicFieldInjection n (EuclideanSpace.single i 1)

def anisotropicMagnetization (D : AnisotropicSpinModel n) (s : RSBScheme k) (j : ℕ)
    (P : AnisotropicParameter n) : Field n :=
  WithLp.toLp 2 (fun i => fderiv ℝ (anisotropicFinitePotential D s j) P
    (anisotropicCoordinateDirection n i))

@[simp] theorem anisotropicMagnetization_apply (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (i : Fin n) :
    anisotropicMagnetization D s j P i=fderiv ℝ (anisotropicFinitePotential D s j) P
      (anisotropicCoordinateDirection n i) := rfl

theorem anisotropicTerminalLinear_coordinate (D : AnisotropicSpinModel n)
    (σ : Configuration n) (i : Fin n) :
    anisotropicTerminalLinear D σ (anisotropicCoordinateDirection n i)=Paper.spinSign (σ i) := by
  rw [anisotropicCoordinateDirection,anisotropicFieldInjection_apply,anisotropicTerminalLinear_apply]
  simp [anisotropicHamiltonian,fieldDot,EuclideanSpace.single_apply]

theorem anisotropicMagnetization_eq_spin_mean (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (i : Fin n) :
    anisotropicMagnetization D s j P i=
      ∫σ,Paper.spinSign (σ i) ∂anisotropicFiniteSpinKernel D s j P := by
  rw [anisotropicMagnetization_apply,fderiv_anisotropicFinitePotential]
  simp_rw [anisotropicTerminalLinear_coordinate]

theorem anisotropicMagnetization_component_bound (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) (i : Fin n) :
    |anisotropicMagnetization D s j P i|≤1 := by
  rw [anisotropicMagnetization_eq_spin_mean]
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := anisotropicFiniteSpinKernel D s j P)
      (f := fun σ => Paper.spinSign (σ i)) (C := (1 : ℝ))
      (.of_forall fun σ => by simp only [Real.norm_eq_abs,Paper.abs_spinSign];exact le_rfl)

theorem boundedJets_anisotropicMagnetization_component (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (i : Fin n) :
    BoundedJets (fun P => anisotropicMagnetization D s j P i) :=
  (boundedPositiveJets_anisotropicFinitePotential D s j).boundedJets_fderiv_apply
    (anisotropicCoordinateDirection n i)

def anisotropicEuclideanMagnetization (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (i : ℕ) (z : AnisotropicGaussianSpace n k) : Field n :=
  anisotropicMagnetization D s (k+2-i) (anisotropicEuclideanStateLinear D s i z)

theorem boundedJets_anisotropicEuclideanMagnetization_component (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (l : Fin n) :
    BoundedJets (fun z => anisotropicEuclideanMagnetization D s i z l) :=
  (boundedJets_anisotropicMagnetization_component D s (k+2-i) l).comp_linear
    (anisotropicEuclideanStateLinear D s i)

theorem anisotropicCoordinateDirection_gauge (η : Configuration n) (i : Fin n) :
    anisotropicParameterGauge η (anisotropicCoordinateDirection n i)=
      Paper.spinSign (η i) • anisotropicCoordinateDirection n i := by
  rw [anisotropicCoordinateDirection,anisotropicFieldInjection_gauge,fieldGauge_single,map_smul]

theorem anisotropicMagnetization_component_gauge (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (η : Configuration n) (j : ℕ) (P : AnisotropicParameter n) (i : Fin n) :
    anisotropicMagnetization D s j (anisotropicParameterGauge η P) i=
      Paper.spinSign (η i)*anisotropicMagnetization D s j P i := by
  let U := anisotropicFinitePotential D s j
  let v := anisotropicCoordinateDirection n i
  have he : (fun r : ℝ => U (anisotropicParameterGauge η P+(r*Paper.spinSign (η i)) • v))=
      fun r => U (P+r • v) := by
    funext r
    have hx : anisotropicParameterGauge η (P+r • v)=
        anisotropicParameterGauge η P+(r*Paper.spinSign (η i)) • v := by
      rw [map_add,map_smul,anisotropicCoordinateDirection_gauge,smul_smul]
    rw [←hx]
    exact anisotropicFinitePotential_gauge D s η j _
  have hU : ContDiff ℝ 2 U := (contDiff_anisotropicFinitePotential D s j).of_le (by simp)
  have hi := hasDerivAt_on_affine_line U hU (anisotropicParameterGauge η P) v 0
  have hi' : HasDerivAt (fun r => U (anisotropicParameterGauge η P+r • v))
      (fderiv ℝ U (anisotropicParameterGauge η P) v) (id 0*Paper.spinSign (η i)) := by
    simpa using hi
  have hh := hi'.comp 0 ((hasDerivAt_id 0).mul_const (Paper.spinSign (η i)))
  simp only [Function.comp_def,id_eq] at hh
  rw [he] at hh
  have hd := hh.unique (hasDerivAt_on_affine_line U hU P v 0)
  simp only [zero_smul,add_zero] at hd
  change fderiv ℝ U (anisotropicParameterGauge η P) v=Paper.spinSign (η i)*fderiv ℝ U P v
  cases hη : η i <;> simp [Paper.spinSign,hη] at hd ⊢ <;> linarith

theorem anisotropicEuclideanMagnetization_component_gauge (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (η : Configuration n) (i : ℕ) (z : AnisotropicGaussianSpace n k) (l : Fin n) :
    anisotropicEuclideanMagnetization D s i (anisotropicGaussianGauge η z) l=
      Paper.spinSign (η l)*anisotropicEuclideanMagnetization D s i z l := by
  simp only [anisotropicEuclideanMagnetization,anisotropicEuclideanStateLinear_gauge,
    anisotropicMagnetization_component_gauge]

end QuantitativeFollowup
