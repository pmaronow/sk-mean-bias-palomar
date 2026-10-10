module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeTransport
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeSquareUniform
public import QuantitativeFollowup.AnisotropicVarianceRestartNodeSquare

@[expose] public section

/-! The finite posterior expectation is the literal physical restarted
coordinate square. Its field derivatives are genuine derivatives of that
physical quantity, with one common modulus for every finite profile. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128

def anisotropicFiniteRestartPosteriorSquare (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (v : ℕ) (i : Fin n) (x : Field n) : ℝ :=
  ∫z,cascadePosteriorRetainedSquare (fun _ : Configuration n=>0)
    (anisotropicSchemeMass (vectorClampedScheme s q q.property))
    (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
    (k+2) v (cavityCoordinateFeature i)
    (anisotropicEnergyMap D (anisotropicDisorderInjection n g+anisotropicFieldInjection n x)) z
    ∂cascadePosteriorGaussianLaw (fun _ : Configuration n=>0)
      (anisotropicSchemeMass (vectorClampedScheme s q q.property))
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
      (k+2) (anisotropicEnergyMap D (anisotropicDisorderInjection n g+anisotropicFieldInjection n x))

theorem anisotropicFiniteRestartPosteriorSquare_eq_physical (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (v : ℕ) (hv : v≤k+2) (hqv : (q:ℝ) ≤ s.q v) (i : Fin n) (x : Field n) :
    anisotropicFiniteRestartPosteriorSquare D s g q v i x=
      cavityFiniteConditionalCoordinateSquare D (vectorClampedScheme s q q.property) (k+2)
        (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i
        (anisotropicSchemeNode s v hv) := by
  let y:=anisotropicInverseNoiseMap D x
  have hy : anisotropicUnitInput D y=anisotropicFieldInjection n x := by
    simp only [y,anisotropicUnitInput,ContinuousLinearMap.comp_apply,anisotropicNoiseMap_inverseNoise]
  have he:=integral_anisotropicFiniteRestart_retained_square D s g q y v (cavityCoordinateFeature i)
  rw [hy] at he
  unfold anisotropicFiniteRestartPosteriorSquare
  rw [he]
  have hx := cavityFiniteRestartCoordinateSquare_node D s g q y v hv hqv i
  rw [hy] at hx
  rw [hx]
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    have hindex : (Fin.ofNat (k+3) v).val=v := by
      change v%(k+3)=v
      exact Nat.mod_eq_of_lt (by omega)
    have hp : historyExtended (anisotropicFiniteRestartEnergyHistory D s g q y sample) v=
        anisotropicEnergyMap D (anisotropicFiniteRestartPhysicalParameter D s g q y
          (anisotropicRestartElapsed s q v) sample) := by
      simp only [historyExtended,anisotropicFiniteRestartEnergyHistory,
        anisotropicFiniteRestartPhysicalHistory,historySample,hindex]
    dsimp only
    rw [hp,fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean _ _ (anisotropicSchemeMass_nonneg _)]
    congr 1
    rw [←anisotropicFiniteFeatureMean_clamped_node D s q v hv hqv]
    rfl

theorem differentiable_anisotropicFiniteRestartPosteriorSquare (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (v : ℕ) (i : Fin n) : Differentiable ℝ (anisotropicFiniteRestartPosteriorSquare D s g q v i) := by
  let cs:=vectorClampedScheme s q q.property
  let L:=fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D cs l)
  let G:=fun H=>∫z,cascadePosteriorRetainedSquare (fun _ : Configuration n=>0)
    (anisotropicSchemeMass cs) L (k+2) v (cavityCoordinateFeature i) H z
    ∂cascadePosteriorGaussianLaw (fun _ : Configuration n=>0) (anisotropicSchemeMass cs) L (k+2) H
  have hG : Differentiable ℝ G := fun H=>(hasFDerivAt_cascadePosterior_retained_square
    (fun _ : Configuration n=>0) (anisotropicSchemeMass cs) (anisotropicSchemeMass_nonneg cs)
    (anisotropicSchemeMass_le_one cs 0) (antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step cs))
    L (k+2) v (cavityCoordinateFeature i) H).differentiableAt
  exact hG.comp ((anisotropicEnergyMap D).differentiable.comp
    ((differentiable_const (anisotropicDisorderInjection n g)).add (anisotropicFieldInjection n).differentiable))

end QuantitativeFollowup
