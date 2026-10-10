module
public import QuantitativeFollowup.ScalarTransportNodeScheduledDerivative
public import QuantitativeFollowup.ScalarTransportGaussianCovariance
public import QuantitativeFollowup.ScalarFiniteGaussianGamma
public import QuantitativeFollowup.ScalarFiniteUniformGaussianBounds

@[expose] public section

/-! The literal density and observable parameter families for scalar level
transport. Their Gaussian expectations are identified with the constructed
physical diffusion moment throughout the increasing-transport neighborhood. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ContDiff
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarTransportNodeGradient (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (i : ℕ) (u x : ℝ) : ℝ :=
  Paper.parisiGradient β (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
    ((scalarLevelTransport φ u (scalarSchemeTransportNode s i):ℝ),x)

def scalarTransportEuclideanExponent (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (e : Bool) (u : ℝ) (x : QuantitativePaper.Field (k+3)) : ℝ :=
  Paper.spinSign e*x (Fin.last (k+2))-
    ∑i : Fin (k+1),(s.m (i+1)-s.m i)*scalarTransportNodePotential s β φ (i+1) u (x ⟨i+1,by omega⟩)

def scalarTransportGradientSquare (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) (u : ℝ)
    (x : QuantitativePaper.Field (k+3)) : ℝ :=
  scalarTransportNodeGradient s β φ p u (x p)^2

theorem scalarTransportScheme_clock (s : RSBScheme k) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (u : ℝ) (hu : |u| *L<1)
    (i : ℕ) (hi : i≤k+2) :
    (FRSB.forwardSchemeTime (scalarTransportScheme s φ L hφ h0 h1 u hu) 1 i:ℝ)=
      (scalarLevelTransport φ u (scalarSchemeTransportNode s i):ℝ) := by
  rw [scalarSchemeHistoryClock_coe _ i hi]
  rfl

theorem scalarTransportEuclideanExponent_eq_actual (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (e : Bool) :
    scalarTransportEuclideanExponent s β φ e u=
      scalarFiniteEuclideanExponent (scalarTransportScheme s φ L hφ h0 h1 u hu) β e := by
  funext x
  unfold scalarTransportEuclideanExponent scalarFiniteEuclideanExponent scalarTransportNodePotential
  have hc (i : Fin (k+1)) := scalarTransportScheme_clock s φ L hφ h0 h1 u hu (i+1) (by omega)
  simp only [scalarTransportScheme_mass,scalarTransportScheme_measure,hc]

theorem scalarTransportGradientSquare_eq_actual (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (p : Fin (k+3)) :
    scalarTransportGradientSquare s β φ p u=
      scalarFiniteGradientSquare (scalarTransportScheme s φ L hφ h0 h1 u hu) β p := by
  funext x
  unfold scalarTransportGradientSquare scalarFiniteGradientSquare scalarTransportNodeGradient
  rw [scalarTransportScheme_measure,scalarTransportScheme_clock s φ L hφ h0 h1 u hu p (by omega)]

theorem scalarTransportObservationNode_eq_actual (s : RSBScheme k)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (p : Fin (k+3)) :
    scalarLevelTransport φ u (scalarSchemeTransportNode s p)=
      scalarFiniteObservationNode (scalarTransportScheme s φ L hφ h0 h1 u hu) p := by
  apply Subtype.ext
  exact (scalarTransportScheme_clock s φ L hφ h0 h1 u hu p (by omega)).symm

theorem scalarTransportGaussian_Gamma (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (p : Fin (k+3)) :
    FRSB.Gamma β (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
      (scalarLevelTransport φ u (scalarSchemeTransportNode s p))=
      (1/2:ℝ)*∑e : Bool,∫z,Real.exp (scalarTransportEuclideanExponent s β φ e u
        (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2) z))*
        scalarTransportGradientSquare s β φ p u
          (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2) z)
          ∂fieldGaussian (k+2) := by
  rw [←scalarTransportScheme_measure s φ L hφ h0 h1 u hu,
    scalarTransportObservationNode_eq_actual s φ L hφ h0 h1 u hu p,
    scalarFiniteGaussian_Gamma (scalarTransportScheme s φ L hφ h0 h1 u hu) β hβ p]
  simp only [scalarTransportEuclideanExponent_eq_actual s β φ L hφ h0 h1 u hu,
    scalarTransportGradientSquare_eq_actual s β φ L hφ h0 h1 u hu,
    scalarTransportGaussianHistory_eq_actual s β φ L hφ h0 h1 u hu,scalarFiniteGaussianInput]

theorem scalarTransportGaussian_normalization (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) :
    (∑e : Bool,∫z,Real.exp (scalarTransportEuclideanExponent s β φ e u
      (scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ u) (k+2) z))
        ∂fieldGaussian (k+2))=2 := by
  simpa only [scalarTransportEuclideanExponent_eq_actual s β φ L hφ h0 h1 u hu,
    scalarTransportGaussianHistory_eq_actual s β φ L hφ h0 h1 u hu,scalarFiniteGaussianInput] using
    scalarFiniteGaussian_normalization (scalarTransportScheme s φ L hφ h0 h1 u hu) β hβ

end QuantitativeFollowup
