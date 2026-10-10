module
public import FourPapersCommon.FiniteStateCascadeDefinitions
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-! Splitting a standard Gaussian on sum-indexed coordinates into its genuine
independent left and right standard Gaussian vectors. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {I J : Type*} [Fintype I] [Fintype J]

def finiteGaussianLeft : FiniteStateGaussianInput (I⊕J)→L[ℝ]FiniteStateGaussianInput I :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z=>WithLp.toLp 2 (fun i=>z (Sum.inl i))
      map_add' := by intro x y;ext i;simp
      map_smul' := by intro c x;ext i;simp }

def finiteGaussianRight : FiniteStateGaussianInput (I⊕J)→L[ℝ]FiniteStateGaussianInput J :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z=>WithLp.toLp 2 (fun i=>z (Sum.inr i))
      map_add' := by intro x y;ext i;simp
      map_smul' := by intro c x;ext i;simp }

def finiteGaussianSplit (z : FiniteStateGaussianInput (I⊕J)) :
    FiniteStateGaussianInput I×FiniteStateGaussianInput J :=
  (finiteGaussianLeft z,finiteGaussianRight z)

theorem measurable_finiteGaussianSplit : Measurable (finiteGaussianSplit (I:=I) (J:=J)) :=
  (finiteGaussianLeft.continuous.prodMk finiteGaussianRight.continuous).measurable

theorem stdGaussian_map_finiteGaussianSplit :
    (stdGaussian (FiniteStateGaussianInput (I⊕J))).map finiteGaussianSplit=
      (stdGaussian (FiniteStateGaussianInput I)).prod (stdGaussian (FiniteStateGaussianInput J)) := by
  have hc := (measurePreserving_sumPiEquivProdPi (fun _ : I⊕J=>gaussianReal 0 1)).map_eq
  rw [←map_pi_eq_stdGaussian,Measure.map_map measurable_finiteGaussianSplit (by fun_prop)]
  have he : finiteGaussianSplit ∘ WithLp.toLp 2=
      Prod.map (WithLp.toLp 2 : (I→ℝ)→FiniteStateGaussianInput I)
        (WithLp.toLp 2 : (J→ℝ)→FiniteStateGaussianInput J) ∘
        MeasurableEquiv.sumPiEquivProdPi (fun _ : I⊕J=>ℝ) := rfl
  rw [he,←Measure.map_map (by fun_prop) (MeasurableEquiv.sumPiEquivProdPi (fun _ : I⊕J=>ℝ)).measurable,hc,
    ←Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),map_pi_eq_stdGaussian,map_pi_eq_stdGaussian]

theorem hasLaw_finiteGaussianSplit : HasLaw (finiteGaussianSplit (I:=I) (J:=J))
    ((stdGaussian (FiniteStateGaussianInput I)).prod (stdGaussian (FiniteStateGaussianInput J)))
    (stdGaussian (FiniteStateGaussianInput (I⊕J))) :=
  ⟨measurable_finiteGaussianSplit.aemeasurable,stdGaussian_map_finiteGaussianSplit⟩

end FourPapersCommon
