module
public import QuantitativePaper.VectorInterpolationKernelTransport
public import FourPapersCommon.FiniteStateCascadeExpectations

@[expose] public section

/-! Every finite cascade terminal-spin mean is the actual vector backward
conditional mean at the corresponding retained-state node. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorInterpolationStateMap_apply (β t : ℝ) (p : VectorState n)
    (σ : Configuration n) :
    vectorInterpolationStateMap β t p σ=vectorTerminalExponent n β t p.1 p.2 σ := by
  simp only [vectorInterpolationStateMap,vectorInterpolationState,PiLp.add_apply,
    PiLp.smul_apply,smul_eq_mul,vectorDisorderFieldEmbedding,vectorSpinFieldEmbedding,
    LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,AddHom.coe_mk,
    WithLp.ofLp_toLp,energyLinear_apply,vectorTerminalExponent]
  ring

theorem vectorInterpolation_terminal_gibbs_mean (β t : ℝ) (p : VectorState n)
    (d : Configuration n→ℝ) :
    (∫σ,d σ∂finiteStateGibbsKernel (fun _ : Configuration n=>0)
      (vectorInterpolationStateMap β t p))=
      terminalMean (vectorTerminalExponent n β t p.1 p.2) d := by
  rw [integral_finiteStateGibbsKernel]
  simp only [gtStateGibbs,gtStatePartition,add_zero,
    vectorInterpolationStateMap_apply,terminalMean,terminalWeight,terminalPartition]

theorem vectorRootInterpolation_gibbs_mean (s : RSBScheme k) (β t a : ℝ)
    (ha : 0≤a) (ht : t≤1) (d : Configuration n→ℝ)
    (j : ℕ) (hj : j≤k+1) (p : VectorState n) :
    (∫σ,d σ∂finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0)
      (vectorRootInterpolationMass s a) (vectorRootInterpolationScaledDirection s β t) j
      (vectorInterpolationStateMap β t p))=
      vectorBackwardMean s β t d (k+2-j) p := by
  let mass:=vectorRootInterpolationMass s a
  let L:=vectorRootInterpolationScaledDirection (n:=n) s β t
  have hmass:=vectorRootInterpolationMass_nonneg s a ha
  have hm (j : ℕ) : IsMarkovKernel (finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0) mass L j):=
    isMarkovKernel_finiteStateCascadeGibbsKernel _ mass hmass L j
  have hK (j : ℕ) : IsMarkovKernel (finiteStateGaussianCascadeKernel mass L
      (gtStateLogPartition (fun _ : Configuration n=>0)) j):=
    isMarkovKernel_finiteStateGaussianTerminalCascadeKernel _ mass hmass L j
  induction j generalizing p with
  | zero=>
    simp only [finiteStateCascadeGibbsKernel,finiteStateCascadeFieldKernel,sourceKernelLaw,
      Kernel.comp_id,Nat.sub_zero]
    rw [vectorBackwardMean_terminal]
    exact vectorInterpolation_terminal_gibbs_mean β t p d
  | succ j ih=>
    haveI:=hm j
    haveI:=hK j
    have hd : Measurable d:=measurable_of_finite _
    have hb (σ : Configuration n) : |d σ|≤∑τ : Configuration n,|d τ|:=
      Finset.single_le_sum (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ σ)
    have heK : finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0) mass L (j+1)=
      finiteStateCascadeGibbsKernel (fun _ : Configuration n=>0) mass L j ∘ₖ
        finiteStateGaussianCascadeKernel mass L (gtStateLogPartition (fun _=>0)) j := by
      simp only [finiteStateCascadeGibbsKernel,finiteStateCascadeFieldKernel,sourceKernelLaw,
        Kernel.comp_assoc]
    rw [heK,Kernel.integral_comp (source_bounded_integrable _ d hd _ hb)]
    have hi : k+1-j∈Icc 1 (k+1):=by constructor <;> omega
    have hid : k+1-(k+1-j)=j:=by omega
    have htransport:=vectorProfileKernel_spin_field_map s β t a ha ht
      (k+1-j) hi.1 hi.2 p
    rw [hid] at htransport
    rw [←htransport]
    have hgm : Measurable (fun y=>∫σ,d σ∂finiteStateCascadeGibbsKernel
        (fun _ : Configuration n=>0) mass L j y):=(hd.stronglyMeasurable.integral_kernel).measurable
    rw [integral_map (measurable_vectorInterpolationStateMap β t).aemeasurable hgm.aestronglyMeasurable]
    dsimp only [mass,L]
    simp_rw [ih (by omega)]
    have hi' : k+2-(j+1)=k+1-j:=by omega
    have hi'' : k+2-j=(k+1-j)+1:=by omega
    rw [hi',vectorBackwardMean_kernel,hi'']

end QuantitativePaper
