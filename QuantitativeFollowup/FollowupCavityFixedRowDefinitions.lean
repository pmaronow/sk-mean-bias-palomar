module
public import QuantitativeFollowup.FollowupCavityRecordedDensity
public import QuantitativeFollowup.FollowupCavityCppZeroResponseObservableData
public import QuantitativeFollowup.AnisotropicBinaryFeatureFinite
public import QuantitativeFollowup.FollowupCavityParameters
public import QuantitativeFollowup.FollowupCavityIncidentRow
public import FourPapersCommon.FiniteObservationTreeLeafPruning

@[expose] public section

/-! A deterministic physical incident row, retaining the entire finite
Gaussian field record and its terminal spin. The row is an energy offset;
the root Gaussian tilt uses the actual fractional outer mass. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}

def cavityFixedRowOffset (n : ℕ) : Field n →L[ℝ] FiniteStateField (Configuration (n+1)) :=
  ∑i : Fin n, (EuclideanSpace.proj i).smulRight
    (anisotropicPairFeature (followupCavityIncidentIndex i))

@[simp] theorem cavityFixedRowOffset_apply (theta : Field n) :
    cavityFixedRowOffset n theta = ∑i : Fin n, theta i •
      anisotropicPairFeature (followupCavityIncidentIndex i) := by
  simp only [cavityFixedRowOffset,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply]
  rfl

def cavityFixedRowLaw (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (theta : Field n) :=
  finiteCascadeTreeGaussianJointLaw (fun _ : Configuration (n+1) => 0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a
    (observationLinearTree (k+2)) (anisotropicRootEnergyMap D)
    (cavityFixedRowOffset n theta)

def cavityFixedRowNormalizer (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (theta : Field n) : ℝ :=
  finiteCascadeTreeGaussianNormalizer (fun _ : Configuration (n+1) => 0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) a (k+2)
    (anisotropicRootEnergyMap D) (cavityFixedRowOffset n theta)

theorem cavityFixedRowNormalizer_pos (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (theta : Field n) :
    0 < cavityFixedRowNormalizer D s a theta :=
  finiteCascadeTreeGaussianNormalizer_pos _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _

instance cavityFixedRowLaw_probability (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (theta : Field n) :
    IsProbabilityMeasure (cavityFixedRowLaw D s a theta) :=
  finiteCascadeTreeGaussianJointLaw_probability _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _

/-- The field at a literal remaining recursion depth, including the root. -/
@[reducible] def cavityFixedRowLineField {E S : Type} : (j : ℕ) → ℕ → E →
    Records E S (observationLinearTree j) → E
  | 0, _, H, _ => H
  | j+1, d, H, r => if d = j+1 then H else cavityFixedRowLineField j d r.1 r.2

def cavityFixedRowLastSquare (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (d : ℕ) (z : FiniteStateField (Configuration (n+1)) ×
      Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1))
        (observationLinearTree (k+2))) : ℝ :=
  (cavityFiniteEnergyFeatureMean (fun _ : Configuration (n+1) => 0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) d
    (WithLp.toLp 2 (fun sigma : Configuration (n+1) => Paper.spinSign (sigma (Fin.last n))))
    (cavityFixedRowLineField (k+2) d z.1 z.2))^2

def cavityFixedRowRestSquare (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (d : ℕ) (z : FiniteStateField (Configuration (n+1)) ×
      Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1))
        (observationLinearTree (k+2))) : ℝ :=
  cavityFiniteEnergyRestOverlap (fun _ : Configuration (n+1) => 0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) d
    (fun i : Fin n => WithLp.toLp 2 (fun sigma : Configuration (n+1) => Paper.spinSign (sigma i.castSucc)))
    (cavityFixedRowLineField (k+2) d z.1 z.2)

end QuantitativeFollowup
