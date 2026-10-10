module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVarianceFieldFeatures

@[expose] public section

/-! The literal energy-field continuation transports to the independent
parameter continuations. This includes arbitrary zero and repeated steps. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets SpinGlass.AT OverlapPaper
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem cavityFiniteEnergyExpectation_at_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (d j : ℕ) (F : FiniteStateField (QuantitativePaper.Configuration n)→ℝ)
    (hF : Measurable F) (P : AnisotropicParameter n) :
    sourceKernelExpectation
      (fun r=>finiteStateGaussianCascadeKernel (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) (gtStateLogPartition (fun _ : QuantitativePaper.Configuration n=>0)) (d+r))
      j F (anisotropicEnergyMap D P)=
    sourceKernelExpectation (fun r=>anisotropicDepthKernel D s (d+r)) j
      (fun Q=>F (anisotropicEnergyMap D Q)) P :=by
  have ht:=sourceKernelExpectation_finiteStateCascade_comp_linear (anisotropicEnergyMap D)
    (anisotropicSchemeInput D s) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (gtStateLogPartition (fun _ : QuantitativePaper.Configuration n=>0)) (finiteStateGaussianTerminal_lipschitz _)
    d j F hF P
  rw [←anisotropicDepthKernel_eq_parameterCascadeKernel D s] at ht
  exact ht

private theorem sourceExpectation_one {E : Type} [MeasurableSpace E] (K : ℕ→Kernel E E)
    (hK : ∀j,IsMarkovKernel (K j)) (j : ℕ) (x : E) :
    sourceKernelExpectation K j (fun _=>1) x=1 :=by
  induction j generalizing x with
  | zero=>rfl
  | succ j ih=>
    haveI:=hK j
    simp only [sourceKernelExpectation]
    simp_rw [ih]
    simp only [integral_const,probReal_univ,smul_eq_mul,mul_one]

def cavityLastVarianceScalarSquareMean (s : RSBScheme k) (b : ℝ) (d j : ℕ) (x : ℝ) : ℝ :=
  sourceKernelExpectation (fun r=>cavityScalarDepthKernel s (Real.sqrt b) (d+r)) j
    (fun y=>(parisiFDeriv s (Real.sqrt b) d y)^2) x

def cavityLastVarianceRestSquareMean (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (d j : ℕ) (P : AnisotropicParameter n) : ℝ :=
  sourceKernelExpectation
    (fun r=>anisotropicDepthKernel (followupCavityRestSpinModel n β ρ hβ hρ) s (d+r)) j
    (cavityLastVarianceRestOverlap s n β ρ hβ hρ d) P

theorem cavityLastVariance_energy_product_mean (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (d j : ℕ)
    (P : AnisotropicParameter (n+1)) :
    let D:=cavityLastVarianceModel n β ρ hβ hρ b hb
    sourceKernelExpectation
      (fun r=>finiteStateGaussianCascadeKernel (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
        (gtStateLogPartition (fun _ : QuantitativePaper.Configuration (n+1)=>0)) (d+r)) j
      (fun H=>cavityFixedRowLastFieldSquare D s d H*cavityFixedRowRestFieldSquare D s d H)
      (anisotropicEnergyMap D P)=
    cavityLastVarianceScalarSquareMean s b d j (P (Sum.inr (Fin.last n)))*
      cavityLastVarianceRestSquareMean s n β ρ hβ hρ d j (cavityRestParameterProjection n P) :=by
  dsimp only
  let D:=cavityLastVarianceModel n β ρ hβ hρ b hb
  rw [cavityFiniteEnergyExpectation_at_parameter D s d j
    (fun H=>cavityFixedRowLastFieldSquare D s d H*cavityFixedRowRestFieldSquare D s d H)
    ((boundedJets_cavityFixedRowLastFieldSquare D s d).1.continuous.measurable.mul
      (boundedJets_cavityFixedRowRestFieldSquare D s d).1.continuous.measurable)]
  dsimp only [D]
  simp_rw [cavityLastVarianceLastFieldSquare_at_parameter,cavityLastVarianceRestFieldSquare_at_parameter]
  have hc:(fun Q:AnisotropicParameter (n+1)=>
      (parisiFDeriv s (Real.sqrt b) d (Q (Sum.inr (Fin.last n))))^2*
        cavityLastVarianceRestOverlap s n β ρ hβ hρ d (cavityRestParameterProjection n Q))=
      fun Q=>cavityLastVarianceRestOverlap s n β ρ hβ hρ d (cavityRestParameterProjection n Q)*
        (parisiFDeriv s (Real.sqrt b) d (Q (Sum.inr (Fin.last n))))^2:=by funext Q;exact mul_comm _ _
  rw [hc,cavityLastVariance_depthExpectation_product s n β ρ hβ hρ b hb d j _ _
    (measurable_cavityLastVarianceRestOverlap s n β ρ hβ hρ d)
    ((parisiF_C2_props s (Real.sqrt b) d).2.1.pow_const 2)]
  exact mul_comm _ _

theorem cavityLastVariance_energy_last_mean (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (d j : ℕ)
    (P : AnisotropicParameter (n+1)) :
    let D:=cavityLastVarianceModel n β ρ hβ hρ b hb
    sourceKernelExpectation
      (fun r=>finiteStateGaussianCascadeKernel (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
        (gtStateLogPartition (fun _ : QuantitativePaper.Configuration (n+1)=>0)) (d+r)) j
      (cavityFixedRowLastFieldSquare D s d) (anisotropicEnergyMap D P)=
    cavityLastVarianceScalarSquareMean s b d j (P (Sum.inr (Fin.last n))) :=by
  dsimp only
  let D:=cavityLastVarianceModel n β ρ hβ hρ b hb
  rw [cavityFiniteEnergyExpectation_at_parameter D s d j _
    (boundedJets_cavityFixedRowLastFieldSquare D s d).1.continuous.measurable]
  dsimp only [D]
  simp_rw [cavityLastVarianceLastFieldSquare_at_parameter]
  have ht:=cavityLastVariance_depthExpectation_product s n β ρ hβ hρ b hb d j
    (fun _=>1) (fun y=>(parisiFDeriv s (Real.sqrt b) d y)^2) measurable_const
    ((parisiF_C2_props s (Real.sqrt b) d).2.1.pow_const 2) P
  simp only [one_mul] at ht
  rw [sourceExpectation_one _ (fun r=>by infer_instance),one_mul] at ht
  exact ht


theorem cavityLastVariance_energy_rest_mean (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (d j : ℕ)
    (P : AnisotropicParameter (n+1)) :
    let D:=cavityLastVarianceModel n β ρ hβ hρ b hb
    sourceKernelExpectation
      (fun r=>finiteStateGaussianCascadeKernel (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
        (gtStateLogPartition (fun _ : QuantitativePaper.Configuration (n+1)=>0)) (d+r)) j
      (cavityFixedRowRestFieldSquare D s d) (anisotropicEnergyMap D P)=
    cavityLastVarianceRestSquareMean s n β ρ hβ hρ d j (cavityRestParameterProjection n P) :=by
  dsimp only
  let D:=cavityLastVarianceModel n β ρ hβ hρ b hb
  rw [cavityFiniteEnergyExpectation_at_parameter D s d j _
    (boundedJets_cavityFixedRowRestFieldSquare D s d).1.continuous.measurable]
  dsimp only [D]
  simp_rw [cavityLastVarianceRestFieldSquare_at_parameter]
  have ht:=cavityLastVariance_depthExpectation_product s n β ρ hβ hρ b hb d j
    (cavityLastVarianceRestOverlap s n β ρ hβ hρ d) (fun _=>1)
    (measurable_cavityLastVarianceRestOverlap s n β ρ hβ hρ d) measurable_const P
  simp only [mul_one] at ht
  rw [sourceExpectation_one _ (fun r=>by infer_instance),mul_one] at ht
  exact ht

end QuantitativeFollowup
